var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ,]/g;
window.onload=function (){
  console.clear();
  document.getElementById('input').value=testTerms.map(function(t){return "expand "+t+" 2";}).join("\n");
  document.getElementById('input').onkeydown=handlekey;
  document.getElementById('input').onfocus=handlekey;
  document.getElementById('input').onmousedown=handlekey;
}

function normalizeAbbreviations(s){
  return (s instanceof Term?s:new Term(s+""))+"";
}
function abbreviate(s,abbreviate){
  return (s instanceof Term?s:new Term(s+"")).toString(typeof abbreviate=="object"?abbreviate:true);
}

function Scanner(s){
  if (s instanceof Scanner) return s.clone();
  if (typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof Scanner)) return new Scanner(s);
  this.s=s;
  this.pos=0;
  this.length=s.length;
  return this;
}
Scanner.prototype.clone=function (){
  return new Scanner(this.s);
}
Scanner.prototype.next=function (){
  if (this.pos>=this.length) return null;
  var c=this.s.charAt(this.pos);
  ++this.pos;
  return c;
}
Scanner.prototype.nextNumber=function (){
  var s=this.s.substring(this.pos);
  var m=s.match(/^[0-9]+/);
  if (m) {
    this.pos+=m[0].length;
    return Number(m[0]);
  }
  return null;
}
Scanner.prototype.peek=function (length,offset){
  if (typeof length=="undefined") length=1;
  if (typeof offset=="undefined") offset=0;
  if (this.pos+offset>this.length) return null;
  return this.s.substring(this.pos+offset,this.pos+offset+length);
}
Scanner.prototype.move=function (n){
  this.pos+=n;
}
Scanner.prototype.hasNext=function (){
  return this.pos<this.length;
}
Scanner.prototype.finished=function (){
  return this.pos>=this.length;
}
Object.defineProperty(Scanner.prototype,"constructor",{
  value:Scanner,
  enumerable:false,
  writable:true
});

/**
 * @constructor
 * @param {*} s 
 * @returns {Term}
 */
function Term(s){
  if (s instanceof Term) return s.clone();
  else if (typeof s!="undefined"&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof Term)) return new Term(s);
  if (s) return Term.build(s);
  else return this;
}
/**
 * @param {Term|string|Scanner} s 
 * @param {number=} context 
 * @returns {Term}
 */
Term.build=function (s,context){
  if (s instanceof Term) return s.clone();
  function appendToRSum(term){
    if (state==START) r=term;
    else if (state==PLUS) r=SumTerm.buildNoClone([r,term]);
    else throw Error("Wrong state when attempting to append as sum");
    state=CLOSEDTERM;
  }
  var scanner;
  if (typeof s=="string") scanner=new Scanner(s);
  else if (s instanceof Scanner) scanner=s;
  else throw Error("Invalid expression: "+s);
  var nums="0123456789";
  var symbols="+(){}^_";
  var notword=nums+symbols;
  var NUMBER=0;
  var SYMBOL=1;
  var WORD=2;
  var symbolTypes=["NUMBER","SYMBOL","WORD"];
  /** @type {Term} */
  var r=null;
  var startpos=scanner.pos;
  var TOP=0;
  var PSITERMSUPERSCRIPT=1;
  var LETTERTERMSUPERSCRIPT=2;
  var LETTERTERMSUBSCRIPT=3;
  var LETTERTERMINNER=4;
  var CLASSSUBSCRIPT=5;
  var BRACES=6;
  var contextNames=["TOP","PSITERMSUPERSCRIPT","LETTERTERMSUPERSCRIPT","LETTERTERMSUBSCRIPT","LETTERTERMINNER","CLASSSUBSCRIPT","BRACES"];
  if (typeof context=="undefined") context=TOP;
  var START=0;
  var PLUS=1;
  var CLOSEDTERM=2;
  var EXIT=3;
  var stateNames=["START","PLUS","CLOSEDTERM","EXIT"];
  var state=START;
  while (scanner.hasNext()&&state!=EXIT){
    var scanpos=scanner.pos;
    var next=scanner.next();
    var nextWord=next;
    var symbolType;
    if (nums.indexOf(nextWord)!=-1){
      while (scanner.hasNext()&&nums.indexOf(scanner.peek())!=-1){
        nextWord+=scanner.next();
      }
      symbolType=NUMBER;
    }else if (symbols.indexOf(nextWord)!=-1){
      symbolType=SYMBOL;
    }else{
      while (scanner.hasNext()&&notword.indexOf(scanner.peek())==-1){
        nextWord+=scanner.next();
      }
      symbolType=WORD;
    }
    if (symbolType==NUMBER){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var num=+nextWord;
      if (num==0){
        appendToRSum(ZeroTerm.build());
      }else if (num==1){
        appendToRSum(Term.ONE.clone());
      }else{
        var decomposed=[];
        if (state==PLUS) decomposed.push(r);
        for (var i=0;i<num;i++){
          decomposed.push(Term.ONE.clone());
        }
        r=SumTerm.buildNoClone(decomposed);
        state=CLOSEDTERM;
      }
    }else if (nextWord=="ω"||nextWord=="w"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(Term.SMALLOMEGA.clone());
    }else if (nextWord=="Ω"||nextWord=="W"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (scanner.peek()=="_"){
        scanner.move(1);
        var subscriptterm=Term.build(scanner,CLASSSUBSCRIPT);
        if (subscriptterm.equal(Term.ZERO)){
          throw Error("Invalid expression "+scanner.s.substring(scanpos,scanner.pos)+" at position "+scanpos+" in expression "+scanner.s);
        }else if (subscriptterm.equal(Term.ONE)){
          appendToRSum(Term.LARGEOMEGA.clone());
        }else if (isSumAndTermsSatisfy(subscriptterm,equalFunc(Term.ONE))){
          if (subscriptterm.terms.length==2){
            appendToRSum(PhiTerm.buildNoClone(Term.ONE.clone(),ZeroTerm.build(),Term.ONE.clone()));
          }else{
            appendToRSum(PhiTerm.buildNoClone(Term.ONE.clone(),ZeroTerm.build(),SumTerm.buildNoClone(subscriptterm.terms.slice(1))));
          }
        }else{
          appendToRSum(PhiTerm.buildNoClone(Term.ONE.clone(),ZeroTerm.build(),subscriptterm));
        }
      }else appendToRSum(Term.LARGEOMEGA.clone());
    }else if (nextWord=="M"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (scanner.peek()=="_"){
        scanner.move(1);
        var subscriptterm=Term.build(scanner,CLASSSUBSCRIPT);
        appendToRSum(PhiTerm.buildNoClone(Term.build("2"),ZeroTerm.build(),subscriptterm));
      }else appendToRSum(Term.M.clone());
    }else if (nextWord=="I"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (scanner.peek()=="_"){
        scanner.move(1);
        var subscriptterm=Term.build(scanner,CLASSSUBSCRIPT);
        appendToRSum(ChiTerm.buildNoClone(Term.M.clone(),ZeroTerm.build(),subscriptterm));
      }else appendToRSum(Term.I.clone());
    }else if (nextWord=="K"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (scanner.peek()=="_"){
        scanner.move(1);
        var subscriptterm=Term.build(scanner,CLASSSUBSCRIPT);
        appendToRSum(PhiTerm.buildNoClone(Term.build("3"),ZeroTerm.build(),subscriptterm));
      }else appendToRSum(Term.K.clone());
    }else if (nextWord=="+"){
      if (state==CLOSEDTERM){
        state=PLUS;
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (nextWord=="φ"||nextWord=="f"||nextWord=="phi"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var nextnext=scanner.next();
      if (nextnext=="^"){
        var superscriptterm=Term.build(scanner,LETTERTERMSUPERSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="_") throw Error("Expected _ at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var subscriptterm=Term.build(scanner,LETTERTERMSUBSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var innerterm=Term.build(scanner,LETTERTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PhiTerm.buildNoClone(superscriptterm,subscriptterm,innerterm));
      }else if (nextnext=="_"){
        var subscriptterm=Term.build(scanner,LETTERTERMSUBSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var innerterm=Term.build(scanner,LETTERTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PhiTerm.buildNoClone(ZeroTerm.build(),subscriptterm,innerterm));
      }else if (nextnext=="("){
        var innerterm=Term.build(scanner,LETTERTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PhiTerm.buildNoClone(ZeroTerm.build(),ZeroTerm.build(),innerterm));
      }else throw Error("Expected ^ or _ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
    }else if (nextWord=="χ"||nextWord=="x"||nextWord=="chi"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var nextnext=scanner.next();
      if (nextnext=="^"){
        var superscriptterm=Term.build(scanner,LETTERTERMSUPERSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="_") throw Error("Expected _ at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var subscriptterm=Term.build(scanner,LETTERTERMSUBSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var innerterm=Term.build(scanner,LETTERTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(ChiTerm.buildNoClone(superscriptterm,subscriptterm,innerterm));
      }else if (nextnext=="_"){
        var subscriptterm=Term.build(scanner,LETTERTERMSUBSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var innerterm=Term.build(scanner,LETTERTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(ChiTerm.buildNoClone(Term.M.clone(),subscriptterm,innerterm));
      }else if (nextnext=="("){
        var innerterm=Term.build(scanner,LETTERTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(ChiTerm.buildNoClone(Term.M.clone(),ZeroTerm.build(),innerterm));
      }else throw Error("Expected ^ or _ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
    }else if (nextWord=="ψ"||nextWord=="p"||nextWord=="psi"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var nextnext=scanner.next();
      if (nextnext=="^"){
        var superscriptterm=Term.build(scanner,PSITERMSUPERSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var innerterm=Term.build(scanner,LETTERTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PsiTerm.buildNoClone(superscriptterm,innerterm));
      }else if (nextnext=="("){
        var innerterm=Term.build(scanner,LETTERTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PsiTerm.buildNoClone(Term.LARGEOMEGA.clone(),innerterm));
      }else throw Error("Expected ^ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
    }else if (nextWord=="{"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character { at position "+scanpos+" in expression "+scanner.s);
      var subterm=Term.build(scanner,BRACES);
      var nextnext=scanner.next();
      if (nextnext!="}") throw Error("Expected closing } at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      appendToRSum(subterm);
    }else{
      throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
    }
    if (state==CLOSEDTERM){
      var peek=scanner.peek();
      if (context==BRACES&&peek=="}"){
        state=EXIT;
      }else if (context==PSITERMSUPERSCRIPT&&peek=="("){
        state=EXIT;
      }else if (context==LETTERTERMSUPERSCRIPT&&peek=="_"){
        state=EXIT;
      }else if (context==LETTERTERMSUBSCRIPT&&peek=="("){
        state=EXIT;
      }else if (context==LETTERTERMINNER&&peek==")"){
        state=EXIT;
      }else if (context==CLASSSUBSCRIPT){
        state=EXIT;
      }
    }
  }
  if (context==TOP){
    if (scanner.hasNext()) throw Error("Something went wrong");
    if (state==START) r=ZeroTerm.build();
    else if (state==PLUS) throw Error("Unexpected end of input");
    else if (state==CLOSEDTERM){}
  }else{
    if (state==START) r=ZeroTerm.build();
    else if (state==PLUS) throw Error("Something went wrong");
    else if (state==CLOSEDTERM){}
  }
  return r;
}
/** @returns {Term} */
Term.buildNoClone=function (){
  throw Error("Not implemented");
}
/** @returns {Term} */
Term.prototype.clone=function (){
  throw Error("Cloning undefined for this term type.");
}
/**
 * @param {boolean} abbreviate
 * @returns {string}
 */
Term.prototype.toString=function (abbreviate){
  throw Error("Stringification undefined for this term type.");
}
/**
 * @param {boolean} abbreviate 
 * @returns {string}
 */
Term.prototype.toStringWithImplicitBrace=function (abbreviate){
  return this.toString(abbreviate);
}
/** @returns {boolean} */
Term.prototype.equal=function (other){
  throw Error("Equality undefined for this term type.");
}
Object.defineProperty(Term.prototype,"constructor",{
  value:Term,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s 
 * @returns {NullTerm}
 */
function NullTerm(s){
  if (s instanceof NullTerm) return s.clone();
  else if (typeof s!="undefined"&&s!==null) throw Error("Invalid expression: "+s);
  if (!(this instanceof NullTerm)) return new NullTerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof NullTerm)) throw Error("Invalid expression: "+s);
}
Object.assign(NullTerm,Term);
NullTerm.build=function (){
  var r=new NullTerm();
  return r;
}
NullTerm.buildNoClone=function (){
  var r=new NullTerm();
  return r;
}
NullTerm.prototype=Object.create(Term.prototype);
NullTerm.prototype.clone=function (){
  return NullTerm.build();
}
/** @param {boolean} abbreviate */
NullTerm.prototype.toString=function (abbreviate){
  return "";
}
NullTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof NullTerm;
}
Object.defineProperty(NullTerm.prototype,"constructor",{
  value:NullTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s 
 * @returns {ZeroTerm}
 */
function ZeroTerm(s){
  if (s instanceof ZeroTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof ZeroTerm)) return new ZeroTerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof ZeroTerm)) throw Error("Invalid expression: "+s);
}
Object.assign(ZeroTerm,Term);
ZeroTerm.build=function (){
  var r=new ZeroTerm();
  return r;
}
ZeroTerm.buildNoClone=function (){
  var r=new ZeroTerm();
  return r;
}
ZeroTerm.prototype=Object.create(Term.prototype);
ZeroTerm.prototype.clone=function (){
  return ZeroTerm.build();
}
/** @param {boolean} abbreviate */
ZeroTerm.prototype.toString=function (abbreviate){
  return "0";
}
ZeroTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof ZeroTerm;
}
Object.defineProperty(ZeroTerm.prototype,"constructor",{
  value:ZeroTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s 
 * @returns {PhiTerm}
 */
function PhiTerm(s){
  if (s instanceof PhiTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof PhiTerm)) return new PhiTerm(s);
  /** @type {PhiTerm} */
  Term.call(this,s);
  if (s&&!(this instanceof PhiTerm)) throw Error("Invalid expression: "+s);
  /** @type {Term} */
  this.sup=null;
  /** @type {Term} */
  this.sub=null;
  /** @type {Term} */
  this.inner=null;
}
Object.assign(PhiTerm,Term);
PhiTerm.build=function (sup,sub,inner){
  var r=new PhiTerm();
  r.sup=new Term(sup);
  r.sub=new Term(sub);
  r.inner=new Term(inner);
  return r;
}
/**
 * @param {Term} sup 
 * @param {Term} sub 
 * @param {Term} inner 
 * @returns {PhiTerm}
 */
PhiTerm.buildNoClone=function (sup,sub,inner){
  var r=new PhiTerm();
  r.sup=sup;
  r.sub=sub;
  r.inner=inner;
  return r;
}
PhiTerm.prototype=Object.create(Term.prototype);
PhiTerm.prototype.clone=function (){
  return PhiTerm.build(this.sup,this.sub,this.inner);
}
/** @param {boolean} abbreviate */
PhiTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1"])&&this.equal(Term.ONE)) return "1";
    else if ((abbreviate===true||abbreviate["ω"])&&this.equal(Term.SMALLOMEGA)) return "ω";
    else if (this.sup.equal(Term.ONE)&&this.sub.equal(Term.ZERO)){
      if ((abbreviate===true||abbreviate["Ω_n"])&&this.inner.equal(Term.LARGEOMEGA.inner)) return abbreviate===true||abbreviate["Ω"]?"Ω":"Ω_1";
      else if ((abbreviate===true||abbreviate["Ω_n"])&&this.inner.equal(Term.ONE)) return "Ω_2";
      else if ((abbreviate===true||abbreviate["Ω_n"])&&isSumAndTermsSatisfy(this.inner,equalFunc(Term.ONE))) return "Ω_"+(this.inner.terms.length+1);
      else if (abbreviate===true||abbreviate["Ω_t"]||abbreviate["Ω_ω"]&&equal(this.inner,Term.SMALLOMEGA)) return "Ω_"+this.inner.toStringWithImplicitBrace(abbreviate);
    }else if (this.sup.equal("2")&&this.sub.equal(Term.ZERO)){
      if ((abbreviate===true||abbreviate["M"])&&this.inner.equal(Term.M.inner)) return "M";
      else if ((abbreviate===true||abbreviate["M_t"])) return "M_"+this.inner.toStringWithImplicitBrace(abbreviate);
    }else if (this.sup.equal("3")&&this.sub.equal(Term.ZERO)){
      if ((abbreviate===true||abbreviate["K"])&&this.inner.equal(Term.K.inner)) return "K";
      else if ((abbreviate===true||abbreviate["K_t"])) return "K_"+this.inner.toStringWithImplicitBrace(abbreviate);
    }
    if ((abbreviate===true||abbreviate["2φ"])&&this.sup.equal(Term.ZERO)){
      if ((abbreviate===true||abbreviate["1φ"])&&this.sub.equal(Term.ZERO)) return "φ("+this.inner.toString(abbreviate)+")";
      else return "φ_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
    }
  }
  var superscriptstr=this.sup.toStringWithImplicitBrace(abbreviate);
  if (/^[ΩIKM](_|$)/.test(superscriptstr)) superscriptstr="{"+superscriptstr+"}";
  return "φ^"+superscriptstr+"_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
}
PhiTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof PhiTerm&&this.sup.equal(other.sup)&&this.sub.equal(other.sub)&&this.inner.equal(other.inner);
}
Object.defineProperty(PhiTerm.prototype,"constructor",{
  value:PhiTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s 
 * @returns {ChiTerm}
 */
function ChiTerm(s){
  if (s instanceof ChiTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof ChiTerm)) return new ChiTerm(s);
  /** @type {ChiTerm} */
  Term.call(this,s);
  if (s&&!(this instanceof ChiTerm)) throw Error("Invalid expression: "+s);
  /** @type {Term} */
  this.sup=null;
  /** @type {Term} */
  this.sub=null;
  /** @type {Term} */
  this.inner=null;
}
Object.assign(ChiTerm,Term);
ChiTerm.build=function (sup,sub,inner){
  var r=new ChiTerm();
  r.sup=new Term(sup);
  r.sub=new Term(sub);
  r.inner=new Term(inner);
  return r;
}
/**
 * @param {Term} sup 
 * @param {Term} sub 
 * @param {Term} inner 
 * @returns {ChiTerm}
 */
ChiTerm.buildNoClone=function (sup,sub,inner){
  var r=new ChiTerm();
  r.sup=sup;
  r.sub=sub;
  r.inner=inner;
  return r;
}
ChiTerm.prototype=Object.create(Term.prototype);
ChiTerm.prototype.clone=function (){
  return ChiTerm.build(this.sup,this.sub,this.inner);
}
/** @param {boolean} abbreviate */
ChiTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if (this.sub.equal(Term.ZERO)&&this.sup.equal(Term.M)){
      if ((abbreviate===true||abbreviate["I"])&&this.inner.equal(Term.I.inner)) return "I";
      else if ((abbreviate===true||abbreviate["I_t"])) return "I_"+this.inner.toStringWithImplicitBrace(abbreviate);
    }
    if ((abbreviate===true||abbreviate["2χ"])&&this.sup.equal(Term.M)){
      if ((abbreviate===true||abbreviate["1χ"])&&this.sub.equal(Term.ZERO)) return "χ("+this.inner.toString(abbreviate)+")";
      else return "χ_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
    }
  }
  var superscriptstr=this.sup.toStringWithImplicitBrace(abbreviate);
  if (/^[ΩIKM](_|$)/.test(superscriptstr)) superscriptstr="{"+superscriptstr+"}";
  return "χ^"+superscriptstr+"_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
}
ChiTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof ChiTerm&&this.sup.equal(other.sup)&&this.sub.equal(other.sub)&&this.inner.equal(other.inner);
}
Object.defineProperty(ChiTerm.prototype,"constructor",{
  value:ChiTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s 
 * @returns {PsiTerm}
 */
function PsiTerm(s){
  if (s instanceof PsiTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof PsiTerm)) return new PsiTerm(s);
  /** @type {PsiTerm} */
  Term.call(this,s);
  if (s&&!(this instanceof PsiTerm)) throw Error("Invalid expression: "+s);
  /** @type {Term} */
  this.sup=null;
  /** @type {Term} */
  this.inner=null;
}
Object.assign(PsiTerm,Term);
PsiTerm.build=function (sup,inner){
  var r=new PsiTerm();
  r.sup=new Term(sup);
  r.inner=new Term(inner);
  return r;
}
/**
 * @param {Term} sup 
 * @param {Term} inner 
 * @returns {PsiTerm}
 */
PsiTerm.buildNoClone=function (sup,inner){
  var r=new PsiTerm();
  r.sup=sup;
  r.inner=inner;
  return r;
}
PsiTerm.prototype=Object.create(Term.prototype);
PsiTerm.prototype.clone=function (){
  return PsiTerm.build(this.sup,this.inner);
}
/** @param {boolean} abbreviate */
PsiTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1ψ"])&&this.sup.equal(Term.LARGEOMEGA)) return "ψ("+this.inner.toString(abbreviate)+")";
  }
  return "ψ^"+this.sup.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
}
PsiTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof PsiTerm&&this.sup.equal(other.sup)&&this.inner.equal(other.inner);
}
Object.defineProperty(PsiTerm.prototype,"constructor",{
  value:PsiTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s 
 * @returns {SumTerm}
 */
function SumTerm(s){
  if (s instanceof SumTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof SumTerm)) return new SumTerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof SumTerm)) throw Error("Invalid expression: "+s);
  /** @type {Term[]} */
  this.terms=null;
}
Object.assign(SumTerm,Term);
/** @param {*[]} terms */
SumTerm.build=function (terms){
  var r=new SumTerm();
  r.terms=[];
  for (var i=0;i<terms.length;i++){
    if (terms[i] instanceof SumTerm){
      r.terms=r.terms.concat(new Term(terms[i]).terms);
    }else{
      r.terms.push(new Term(terms[i]));
    }
  }
  return r;
}
/** @param {Term[]} terms */
SumTerm.buildNoClone=function (terms){
  var r=new SumTerm();
  r.terms=[];
  for (var i=0;i<terms.length;i++){
    if (terms[i] instanceof SumTerm){
      r.terms=r.terms.concat(terms[i].terms);
    }else{
      r.terms.push(terms[i]);
    }
  }
  return r;
}
SumTerm.prototype=Object.create(Term.prototype);
SumTerm.prototype.clone=function (){
  return SumTerm.build(this.terms);
}
/** @param {boolean} abbreviate */
SumTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    var strterms=this.terms.map(function (t){return t.toString(abbreviate);});
    if (abbreviate===true||abbreviate["1"]&&abbreviate["n"]){
      for (var i=0;i<strterms.length;i++){
        if (strterms[i]=="1"){
          for (var j=i;j<strterms.length&&strterms[j]=="1";j++);
          strterms.splice(i,j-i,(j-i)+"");
        }
      }
    }
    return strterms.join("+");
  }else{
    return this.terms.join("+");
  }
}
/** @param {boolean} abbreviate */
SumTerm.prototype.toStringWithImplicitBrace=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1"]&&abbreviate["n"])&&isSumAndTermsSatisfy(this,equalFunc(Term.ONE))) return this.toString(abbreviate);
  }
  return "{"+this.toString(abbreviate)+"}";
}
SumTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof SumTerm
    ?this.terms.length==other.terms.length&&this.terms.every(function (e,i){return e.equal(other.terms[i]);})
    :this.terms.length==1&&this.terms[0].equal(other);
}
SumTerm.prototype.getLeft=function (){
  return new Term(this.terms[0]);
}
/** @returns {Term} */
SumTerm.prototype.getNotLeft=function (){
  if (this.terms.length<2) return ZeroTerm.build();
  else if (this.terms.length<=2) return new Term(this.terms[1]);
  else return SumTerm.build(this.terms.slice(1));
}
SumTerm.prototype.getRight=function (){
  return new Term(this.terms[this.terms.length-1]);
}
/** @returns {Term} */
SumTerm.prototype.getNotRight=function (){
  if (this.terms.length<2) return ZeroTerm.build();
  else if (this.terms.length<=2) return new Term(this.terms[0]);
  else return SumTerm.build(this.terms.slice(0,-1));
}
/**
 * @param {number} start 
 * @param {number} end 
 * @returns {Term}
 */
SumTerm.prototype.slice=function (start,end){
  if (start<0) start=this.terms.length+start;
  if (end===undefined) end=this.terms.length;
  if (end<0) end=this.terms.length+end;
  if (start>=end) return NullTerm.build();
  else if (end-start==1) return new Term(this.terms[start]);
  else return SumTerm.build(this.terms.slice(start,end));
}
Object.defineProperty(SumTerm.prototype,"constructor",{
  value:SumTerm,
  enumerable:false,
  writable:true
});

Term.ZERO=new Term("0");
Term.ONE=new Term("φ^0_0(0)");
Term.SMALLOMEGA=new Term("φ^0_0(1)");
Term.LARGEOMEGA=new Term("φ^1_0(0)");
Term.M=new Term("φ^2_0(0)");
Term.I=new Term("χ^{M}_0(0)");
Term.K=new Term("φ^3_0(0)");

/** @returns {boolean} */
function inT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return true; //1
  if (t instanceof SumTerm) return t.terms.every(function (s){return !s.equal("0")&&inPT(s);}); //2
  if (t instanceof PhiTerm) return inT(t.sup)&&inT(t.sub)&&inT(t.inner); //3
  if (t instanceof ChiTerm) return inT(t.sup)&&inT(t.sub)&&inT(t.inner); //4
  if (t instanceof PsiTerm) return inT(t.sup)&&inT(t.inner); //5
  return false;
}
function inPT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return false; //1
  if (t instanceof SumTerm) return false; //2
  if (t instanceof PhiTerm) return inT(t.sup)&&inT(t.sub)&&inT(t.inner); //3
  if (t instanceof ChiTerm) return inT(t.sup)&&inT(t.sub)&&inT(t.inner); //4
  if (t instanceof PsiTerm) return inT(t.sup)&&inT(t.inner); //5
  return false;
}
function inST(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return false; //1
  if (t instanceof SumTerm) return t.getRight().equal(Term.ONE); //2
  if (t instanceof PhiTerm) return t.equal(Term.ONE); //3
  if (t instanceof ChiTerm) return false; //4
  if (t instanceof PsiTerm) return false; //5
  return false;
}
function inRT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return false; //1
  if (t instanceof SumTerm) return false; //2
  if (t instanceof PhiTerm) return !t.sup.equal(Term.ZERO)&&t.sub.equal(Term.ZERO)&&(t.inner.equal(Term.ZERO)||inST(t.inner)); //3
  if (t instanceof ChiTerm) return t.inner.equal(Term.ZERO)||inST(t.inner); //4
  if (t instanceof PsiTerm) return false; //5
  return false;
}
/**
 * @param {Term} t
 * @param {(value:Term,index:number,array:Term[])=>boolean} f
 */
function isSumAndTermsSatisfy(t,f){
  return t instanceof SumTerm&&t.terms.every(f);
}
/**
 * @param {Term|string} X 
 * @param {Term|string} Y 
 */
function equal(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  return X.equal(Y);
}
/**
 * @param {Term|string} X 
 */
function equalFunc(X){
  if (!(X instanceof Term)) X=new Term(X);
  return function(t){return equal(t,X);};
}
/**
 * @param {Term|string} X 
 * @param {Term|string} Y 
 */
function notEqual(X,Y){
  return !equal(X,Y);
}
/**
 * @param {Term|string} X 
 */
function notEqualFunc(X){
  if (!(X instanceof Term)) X=new Term(X);
  return function(t){return notEqual(t,X);};
}
/**
 * @param {Term|string} S 
 * @returns {string}
 */
function pred(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof ZeroTerm||inPT(S)) return "0"; //1
  if (S instanceof SumTerm){ //2
    var a=S.getNotRight();
    var b=S.getRight();
    if (equal(b,"1")) return a+""; //2.1
    else{
      var pred_b=pred(b);
      if (equal(pred_b,"0")) return a+""; //2.2
      else return a+"+"+pred_b; //2.3
    }
  }
  throw Error("No rule to compute pred("+S+")");
}
/**
 * @param {Term|string} S 
 * @returns {string}
 */
function deg(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (!inPT(S)) return "0"; //1
  if (S instanceof PhiTerm) return S.sup+""; //2
  if (S instanceof ChiTerm) return pred(deg(S.sup)); //3
  if (S instanceof PsiTerm) return "0"; //4
  throw Error("No rule to compute deg("+S+")");
}
/**
 * @param {Term|string} S 
 * @returns {[string,string]} 
 */
function index(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof PhiTerm) return [S.sup+"","0"]; //1
  else if (S instanceof ChiTerm){ //2
    var k=S.sup;
    var a=S.sub;
    var b=S.inner;
    if (equal(a,"0")) return index(k); //2.1
    else return [k+"",a+""]; //2.2
  }else return ["0","0"]; //3
  throw Error("No rule to compute index("+S+")");
}
/**
 * @param {Term|string} S 
 * @returns {string} S^+
 */
function termPlus(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof ZeroTerm) return Term.ONE+""; //1
  else if (S instanceof PhiTerm&&equal(S.sup,"1")&&equal(S.sub,"0")&&notEqual(S.inner,"0")) return "φ^"+Term.ONE+"_0("+S.inner+"+"+Term.ONE+")"; //2
  else return "φ^"+Term.ONE+"_0("+S+"+"+Term.ONE+")"; //3
  throw Error("No rule to compute "+S+"^+");
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns {string} S^T_•
 */
function termBullet(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (S instanceof ChiTerm){ //1
    var k=S.sup;
    var a=S.sub;
    var b=S.inner;
    if (equal(k,T)) return a+""; //1.1
    else return termBullet(k,T); //1.2
  }else return "0"; //2
  throw Error("No rule to compute "+S+"^"+T+"_•");
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns S<=T
 */
function lessThanOrEqual(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  return equal(S,T)||lessThan(S,T);
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns {boolean} S<T
 */
function lessThan(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (T instanceof ZeroTerm) return false; //1
  if (S instanceof ZeroTerm) return true; //2
  if (S instanceof SumTerm){
    var a=S.getLeft();
    if (T instanceof SumTerm){ //3
      var c=T.getLeft();
      return lessThan(a,c)|| //3.1
        equal(a,c)&&lessThan(S.getNotLeft(),T.getNotLeft()); //3.2
    }
    if (inPT(T)) return lessThan(a,T); //4
  }
  if (inPT(S)&&T instanceof SumTerm) return !lessThan(T,S); //5
  if (S instanceof PhiTerm){
    var i=S.sup;
    var a=S.sub;
    var b=S.inner;
    if (T instanceof PhiTerm){ //6
      var j=T.sup;
      var c=T.sub;
      var d=T.inner;
      if (equal(i,j)){
        if (equal(a,c)&&lessThan(b,d)) return true; //6.1
        if (lessThan(a,c)&&lessThanOrEqual(b,T)) return true; //6.2
        if (lessThan(c,a)&&lessThan(S,d)) return true; //6.3
      }
      if (lessThan(i,j)){
        if (lessThan(a,T)&&lessThanOrEqual(b,T)) return true; //6.4
        if (equal(a,T)&&equal(b,"0")) return true; //6.5
      }
      if (lessThan(j,i)){
        if ((lessThanOrEqual(S,c)||lessThan(S,d))&&(notEqual(c,S)||notEqual(d,"0"))) return true; //6.6;6.7;6.8;6.9
      }
      return false;
    }
    if (T instanceof ChiTerm){ //7
      var l=T.sup;
      var c=T.sub;
      var d=T.inner;
      if (!lessThan(S,l)) return false;
      if (equal(i,T)&&equal(a,"0")&&equal(b,"0")) return true; //7.1
      if (lessThan(i,T)){
        if (equal(a,T)&&equal(b,"0")) return true; //7.2
        if (lessThan(a,T)&&lessThanOrEqual(b,T)) return true; //7.3
      }
      return false;
    }
    if (T instanceof PsiTerm){ //8
      var l=T.sup;
      var c=T.inner;
      if (!lessThan(S,l)) return false;
      if (equal(i,T)&&equal(a,"0")&&equal(b,"0")) return true; //8.1
      if (lessThan(i,T)){
        if (equal(a,T)&&equal(b,"0")) return true; //8.2
        if (lessThan(a,T)&&lessThanOrEqual(b,T)) return true; //8.3
      }
      return false;
    }
  }
  if (S instanceof ChiTerm){
    var k=S.sup;
    var a=S.sub;
    var b=S.inner;
    if (T instanceof PhiTerm) return !lessThan(T,S); //9
    if (T instanceof ChiTerm){ //10
      var l=T.sup;
      var c=T.sub;
      var d=T.inner;
      if (equal(k,l)){
        if (equal(a,c)&&lessThan(b,d)) return true; //10.1
        if (lessThan(a,c)&&lessThan(termAstGeq(a,l),T)&&lessThan(b,T)) return true; //10.2
        if (lessThan(c,a)){
          if (lessThanOrEqual(S,termAstGeq(c,k))) return true; //10.3
          if (lessThanOrEqual(S,d)) return true; //10.4
        }
      }
      if (lessThanOrEqual(k,T)) return true; //10.5
      if (lessThanOrEqual(S,termMinus(T))) return true; //10.6
      if (lessThan(S,l)&&lessThan(termMinus(S),T)&&lessThan(a,termBullet(l,k))) return true; //10.7
      return false;
    }
    if (T instanceof PsiTerm) return lessThan(S,T.sup)&&triangleLessThan(S,T.sup,T.inner); //11
  }
  if (S instanceof PsiTerm){
    var k=S.sup;
    var a=S.inner;
    if (T instanceof PhiTerm||T instanceof ChiTerm) return !lessThan(T,S); //12;13
    if (T instanceof PsiTerm){ //14
      var l=T.sup;
      var c=T.inner;
      if (equal(k,l)&&lessThan(a,c)) return true; //14.1
      if (lessThan(k,l)&&lessThan(termAstGeq(k,l),T)) return true; //14.2
      if (lessThan(S,l)&&lessThan(l,k)) return true; //14.3
      return false;
    }
  }
  throw Error("No rule to compute if "+S+"<"+T);
}
/**
 * @param {Term|string} S 
 * @param {Term|string} L 
 * @param {Term|string} C 
 * @returns {boolean} S◁(L,C)
 */
function triangleLessThan(S,L,C){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(L instanceof Term)) L=new Term(L);
  if (!inT(S)||!inT(L)||!inT(C)) throw Error("Invalid argument: "+S+","+L+","+C);
  if (S instanceof ZeroTerm) return true; //1
  if (S instanceof SumTerm) return S.terms.every(function(a){return triangleLessThan(a,L,C);}); //2
  if (S instanceof PhiTerm) return triangleLessThan(S.sup,L,C)&&triangleLessThan(S.sub,L,C)&&triangleLessThan(S.inner,L,C); //3
  if (S instanceof ChiTerm) return triangleLessThan(S.sup,L,C)&&triangleLessThan(S.sub,L,C)&&triangleLessThan(S.inner,L,C); //4
  if (S instanceof PsiTerm){ //5
    var k=S.sup;
    var a=S.inner;
    var L_minus=termMinus(L);
    if (lessThanOrEqual(S,L_minus)) return true; //5.1
    if (lessThan(L_minus,S)&&triangleLessThan(a,L,C)){
      if (lessThan(k,L)) return true; //5.2
      if (lessThanOrEqual(L,k)&&lessThan(a,C)&&triangleLessThan(k,L,C)&&triangleLessThan(a,L,C)) return true; //5.3
    }
    return false;
  }
  throw Error("No rule to compute if "+S+"◁("+L+","+C+")");
}
/**
 * @param {Term|string} S 
 * @returns {boolean} S∈OT
 */
function inOT(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)){
    console.warn("Not in T: "+S);
    return false;
  }
  if (S instanceof ZeroTerm) return true; //1
  if (S instanceof SumTerm){ //2
    var a=S.getLeft();
    if (!inOT(a)) return false;
    var b=S.getNotLeft();
    return inOT(b)&&notEqual(b,"0")&&lessThan(b,"φ^0_0("+a+"+"+Term.ONE+")");
  }
  if (S instanceof PhiTerm){ //3
    var i=S.sup;
    var a=S.sub;
    var b=S.inner;
    if (!inOT(i)||!inOT(a)||!inOT(b)) return false;
    if (equal(b,"0")){
      if (!inPT(a)) return true; //3.1
      if (a instanceof PhiTerm) return lessThanOrEqual(a.sup,i); //3.2
      if (a instanceof ChiTerm) return lessThanOrEqual(deg(a.sup),i); //3.3
      if (a instanceof PsiTerm){
        var l=a.sup;
        var c=a.inner;
        return lessThan(deg(l),i)|| //3.4
          l instanceof PhiTerm&&equal(l.sup,i)&&equal(l.sub,"0"); //3.5
      }
    }else if (lessThanOrEqual(b,a)) return true; //3.6
    if (b instanceof SumTerm) return true; //3.7
    if (b instanceof PhiTerm){
      var c=b.sub;
      var d=b.inner;
      if (equal(b.sup,i)&&lessThanOrEqual(c,a)) return true; //3.8
      var j=b.sup;
      if (lessThan(j,i)) return true; //3.9
    }
    if (b instanceof ChiTerm) return lessThanOrEqual(deg(b.sup),i); //3.10
    if (b instanceof PsiTerm){
      var l=b.sup;
      var c=b.inner;
      return lessThan(deg(l),i)|| //3.11
        l instanceof PhiTerm&&equal(l.sup,i)&&equal(l.sub,"0"); //3.12
    }
    return false;
  }
  if (S instanceof ChiTerm){ //4
    var k=S.sup;
    var a=S.sub;
    var b=S.inner;
    if (!inRT(k)||!inOT(k)||!inOT(a)||!inOT(b)||!lessThan(b,k)||equal(pred(deg(k)),"0")||!lessThan(a,"ψ^"+termPlus(k)+"(0)")) return false;
    if (lessThanOrEqual(b,termMinus("χ^"+k+"_"+a+"(0)"))) return true; //4.1
    if (!inPT(b)) return true; //4.2
    if (b instanceof PhiTerm) return lessThan(b.sup,deg(k)); //4.3
    if (b instanceof ChiTerm){
      var l=b.sup;
      var c=b.sub;
      var d=b.inner;
      if (equal(deg(l),deg(k))&&lessThanOrEqual(c,a)) return true; //4.4
      if (lessThan(deg(l),deg(k))) return true; //4.5
    }
    if (b instanceof PsiTerm){
      var l=b.sup;
      var c=b.inner;
      if (!triangleLessThan(a,l,c)) return true; //4.6
      if (l instanceof PhiTerm&&equal(l.sub,"0")&&lessThan(l.sup,deg(k))) return true; //4.7
      if (l instanceof ChiTerm){
        var m=l.sup;
        var e=l.sub;
        var f=l.inner;
        if (equal(deg(m),deg(k))&&lessThanOrEqual(e,a)) return true; //4.8
        if (lessThan(deg(m),deg(k))) return true; //4.9
      }
    }
    return false;
  }
  if (S instanceof PsiTerm) return inRT(S.sup)&&inOT(S.sup)&&inOT(S.inner)&&triangleLessThan(S.inner,S.sup,S.inner); //5
  throw Error("No rule to compute if "+S+"∈OT");
}
/**
 * @param {Term|string} S
 * @param {Term|string} T
 * @returns {string} S^{*≧T}
 */
function termAstGeq(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) S=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (equal(S,"0")||equal(S,T)||!inOT(S)) return "0"; //1
  else{ //2
    if (S instanceof SumTerm){ //2.1
      var a=S.getLeft();
      var b=S.getNotLeft();
      var astGeq_a_T=termAstGeq(a,T);
      var Term_astGeq_a_T=new Term(astGeq_a_T);
      var astGeq_b_T=termAstGeq(b,T);
      var Term_astGeq_b_T=new Term(astGeq_b_T);
      if (lessThanOrEqual(Term_astGeq_a_T,Term_astGeq_b_T)) return astGeq_b_T; //2.1.1
      if (lessThan(Term_astGeq_b_T,Term_astGeq_a_T)) return astGeq_a_T; //2.1.2
    }
    if (S instanceof PhiTerm){ //2.2
      var i=S.sup;
      var a=S.sub;
      var b=S.inner;
      var astGeq_i_T=termAstGeq(i,T);
      var Term_astGeq_i_T=new Term(astGeq_i_T);
      var astGeq_a_T=termAstGeq(a,T);
      var Term_astGeq_a_T=new Term(astGeq_a_T);
      var astGeq_b_T=termAstGeq(b,T);
      var Term_astGeq_b_T=new Term(astGeq_b_T);
      if (lessThanOrEqual(Term_astGeq_i_T,astGeq_b_T)&&lessThanOrEqual(Term_astGeq_a_T,Term_astGeq_b_T)) return astGeq_b_T; //2.2.1
      if (lessThanOrEqual(Term_astGeq_i_T,astGeq_a_T)&&lessThan(Term_astGeq_b_T,Term_astGeq_a_T)) return astGeq_a_T; //2.2.2
      if (lessThan(Term_astGeq_a_T,Term_astGeq_i_T)&&lessThan(Term_astGeq_b_T,Term_astGeq_i_T)) return astGeq_i_T; //2.2.3
    }
    if (S instanceof ChiTerm){ //2.3
      var k=S.sup;
      var a=S.sub;
      var b=S.inner;
      if (lessThanOrEqual(T,k)) return S+""; //2.3.1
      if (lessThan(k,T)){ //2.3.2
        var astGeq_k_T=termAstGeq(k,T);
        var Term_astGeq_k_T=new Term(astGeq_k_T);
        var astGeq_a_T=termAstGeq(a,T);
        var Term_astGeq_a_T=new Term(astGeq_a_T);
        var astGeq_b_T=termAstGeq(b,T);
        var Term_astGeq_b_T=new Term(astGeq_b_T);
        if (lessThanOrEqual(Term_astGeq_k_T,astGeq_b_T)&&lessThanOrEqual(Term_astGeq_a_T,Term_astGeq_b_T)) return astGeq_b_T; //2.3.2.1
        if (lessThanOrEqual(Term_astGeq_k_T,astGeq_a_T)&&lessThan(Term_astGeq_b_T,Term_astGeq_a_T)) return astGeq_a_T; //2.3.2.2
        if (lessThan(Term_astGeq_a_T,Term_astGeq_k_T)&&lessThan(Term_astGeq_b_T,Term_astGeq_k_T)) return astGeq_k_T; //2.3.2.3
      }
    }
    if (S instanceof PsiTerm) return S+""; //2.4
  }
  throw Error("No rule to compute "+S+"^{*≧"+T+"}");
}
/**
 * @param {Term|string} S
 * @returns {string} S^-
 */
function termMinus(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof PhiTerm){
    var i=S.sup;
    var b=S.inner;
    if (equal(S.sub,"0")&&inOT(i)&&inOT(b)){ //1
      if (equal(b,"0")) return i+""; //1.1
      else{ //1.2
        var pred_b=pred(b);
        var fi0pred_b="φ^"+i+"_0("+pred_b+")";
        if (inOT(fi0pred_b)) return fi0pred_b; //1.2.1
        else return pred_b; //1.2.2
      }
    }else return "0"; //3
  }else if (S instanceof ChiTerm){
    var k=S.sup;
    var a=S.sub;
    var b=S.inner;
    if (inOT(k)&&inOT(a)&&inOT(b)){ //2
      if (equal(b,"0")){ //2.1
        var minusGeq_k=termMinus(k);
        var Term_minus_k=new Term(minusGeq_k);
        var astGeq_a_k=termAstGeq(a,k);
        var Term_astGeq_a_k=new Term(astGeq_a_k);
        if (lessThanOrEqual(Term_minus_k,Term_astGeq_a_k)) return astGeq_a_k; //2.1.1
        if (lessThan(Term_astGeq_a_k,Term_minus_k)) return minusGeq_k; //2.1.2
      }else{ //2.2
        var pred_b=pred(b);
        var xkapred_b="χ^"+k+"_"+a+"("+pred_b+")";
        if (inOT(xkapred_b)) return xkapred_b; //2.2.1
        else return pred_b; //2.2.2
      }
    }else return "0"; //3
  }else return "0"; //3
  throw Error("No rule to compute "+S+"^-");
}
/**
 * @param {Term|string} S
 * @returns {string}
 */
function dom(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inOT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm) return dom(S.getRight()); //2
  if (S instanceof PhiTerm){ //3
    var i=S.sup;
    var a=S.sub;
    var b=S.inner;
    var dom_a=dom(a);
    var Term_dom_a=new Term(dom_a);
    var dom_b=dom(b);
    var Term_dom_b=new Term(dom_b);
    if (equal(Term_dom_a,"0")){
      if (equal(dom(i),"0")){
        if (equal(Term_dom_b,"0")) return Term.ONE+""; //3.1
        if (equal(Term_dom_b,"1")) return Term.SMALLOMEGA+""; //3.2
      }else if (equal(Term_dom_b,"0")||equal(Term_dom_b,"1")) return S+""; //3.3
    }else if (equal(Term_dom_a,"1")&&(equal(Term_dom_b,"0")||equal(Term_dom_b,"1"))) return Term.SMALLOMEGA+""; //3.4
    else if (equal(Term_dom_b,"0")||equal(Term_dom_b,"1")) return dom_a; //3.5
    if (!equal(Term_dom_b,"0")&&!equal(Term_dom_b,"1")) return dom_b; //3.6
  }
  if (S instanceof ChiTerm){ //4
    var k=S.sup;
    var a=S.sub;
    var b=S.inner;
    var dom_b=dom(b);
    var Term_dom_b=new Term(dom_b);
    if (equal(Term_dom_b,"0")||equal(Term_dom_b,"1")) return S+""; //4.1
    else return dom_b; //4.2
  }
  if (S instanceof PsiTerm){
    var k=S.sup;
    var a=S.inner;
    var dom_a=dom(a);
    var Term_dom_a=new Term(dom_a);
    if (equal(Term_dom_a,"0")||equal(Term_dom_a,"1")){
      if (inOT("χ^"+k+"_0(0)")) return Term.SMALLOMEGA+""; //5.1
      var index_k=index(k);
      var Term_index_k=index_k.map(Term);
      if (equal(Term_index_k[1],"0")){
        var j=Term_index_k[0];
        var dom_j=dom(j);
        var Term_dom_j=new Term(dom_j);
        if (equal(Term_dom_j,"1")) return Term.SMALLOMEGA+""; //5.2
        else return dom_j; //5.3
      }else{ //5.4
        var l=Term_index_k[0];
        var c=Term_index_k[1];
        var dom_c=dom(c);
        var Term_dom_c=new Term(dom_c);
        if (notEqual(Term_dom_c,"1")&&lessThan(Term_dom_c,l)) return dom_c; //5.4.1
        else return Term.SMALLOMEGA+""; //5.4.2
      }
    }else{
      if (lessThan(Term_dom_a,k)) return dom_a; //5.5
      if (lessThanOrEqual(k,Term_dom_a)) return Term.SMALLOMEGA+""; //5.6
    }
  }
  throw Error("No rule to compute dom("+S+")");
}
/**
 * @param {Term|string} I
 * @param {Term|string} S
 * @param {Term|string} N
 * @returns {string} Γ_I(S,N)
 */
function gamma(I,S,N){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inOT(I)||!inOT(S)||!inOT(N)) throw Error("Invalid argument: "+I+","+S+","+N);
  if (equal(dom(N),"1")) return "φ^"+I+"_"+gamma(I,S,pred(N))+"(0)"; //1
  else if (inOT("φ^"+I+"_"+S+"(0)")) return S+""; //2
  else return S+"+"+Term.ONE; //3
  throw Error("No rule to compute Γ_"+I+"("+S+","+N+")");
}
/**
 * @param {Term|string} I
 * @param {Term|string} A
 * @param {Term|string} B
 * @returns {string} \overline{φ}(I,A,B)
 */
function linePhi(I,A,B){
  if (!(I instanceof Term)) I=new Term(I);
  if (!(A instanceof Term)) A=new Term(A);
  if (!(B instanceof Term)) B=new Term(B);
  if (!inOT(I)||!inOT(A)||!inOT(B)) throw Error("Invalid argument: "+I+","+A+","+B);
  var fIAB="φ^"+I+"_"+A+"("+B+")";
  if (inOT(fIAB)) return fIAB; //1
  else{
    if (equal(B,"0")) return A+""; //2
    else return B+""; //3
  }
  throw Error("No rule to compute \\overline{φ}("+I+","+A+","+B+")");
}
/**
 * @param {Term|string} K
 * @param {Term|string} A
 * @returns {string} ψ^-(K,A)
 */
function psiMinus(K,A){
  if (!(K instanceof Term)) K=new Term(K);
  if (!(A instanceof Term)) A=new Term(A);
  if (!inOT(K)||!inOT(A)) throw Error("Invalid argument: "+K+","+A);
  var dom_A=dom(A);
  var Term_dom_A=new Term(dom_A);
  var minus_K=termMinus(K);
  if (equal(Term_dom_A,"0")&&notEqual(minus_K,"0")) return minus_K+"+"+Term.ONE; //1
  var pkfund_a_0;
  if (equal(Term_dom_A,"1")&&inOT(pkfund_a_0="ψ^"+K+"("+fund(A,"0")+")")) return pkfund_a_0+"+"+Term.ONE; //2
  return minus_K; //3
  throw Error("No rule to compute ψ^-("+K+","+A+")");
}
/**
 * @param {Term|string} S 
 * @param {Term|number|string} n 
 * @returns {string} S[T]
 */
function fund(S,n){
  if (!(S instanceof Term)) S=new Term(S);
  if (typeof n=="number") n=String(n);
  if (!(n instanceof Term)) n=new Term(n);
  var Term_dom_S;
  if (!inOT(S)||!inOT(n)||!(lessThan(n,Term_dom_S=new Term(dom(S)))||lessThan(Term_dom_S,"ω"))) throw Error("Invalid argument: "+S+","+n);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm){ //2
    var a=S.getLeft();
    var b=S.getNotLeft();
    var fund_b_n=fund(b,n);
    if (equal(fund_b_n,"0")) return a+""; //2.1
    else return a+"+"+fund_b_n; //2.2
  }
  if (S instanceof PhiTerm){ //3
    var i=S.sup;
    var a=S.sub;
    var b=S.inner;
    var dom_a=dom(a);
    var Term_dom_a=new Term(dom_a);
    var dom_b=dom(b);
    var Term_dom_b=new Term(dom_b);
    if (equal(Term_dom_a,"0")){
      var dom_i=dom(i);
      var Term_dom_i=new Term(dom_i);
      if (equal(Term_dom_i,"0")){
        if (equal(Term_dom_b,"0")) return "0"; //3.1
        else if (equal(Term_dom_b,"1")){ //3.2
          if (equal(dom(n),"1")) return fund(S,fund(n,"0"))+"+"+linePhi(i,a,fund(b,n)); //3.2.1
          else return linePhi(i,a,fund(b,n)); //3.2.2
        }
      }else if (equal(Term_dom_b,"0")||equal(Term_dom_b,"1")) return n+""; //3.3
    }else if (equal(Term_dom_a,"1")&&(equal(Term_dom_b,"0")||equal(Term_dom_b,"1"))){ //3.4
      if (equal(dom(n),"1")) return "φ^"+i+"_"+fund(a,"0")+"("+fund(S,fund(n,"0"))+")"; //3.4.1
      else if (equal(Term_dom_b,"0")){
        var fund_a_0=fund(a,"0");
        var fifund_a_00="φ^"+i+"_"+fund_a_0+"(0)";
        if (inOT(fifund_a_00)) return fifund_a_00; //3.4.2
        else return fund_a_0+"+"+Term.ONE; //3.4.3
      }else return "φ^"+i+"_"+fund(a,"0")+"("+linePhi(i,a,fund(b,"0"))+"+"+Term.ONE+")"; //3.4.4
    }else if (equal(Term_dom_b,"0")){
      var fund_a_n=fund(a,n);
      var fifund_a_n0="φ^"+i+"_"+fund_a_n+"(0)";
      if (inOT(fifund_a_n0)) return fifund_a_n0; //3.5
      else return fund_a_n+"+"+Term.ONE; //3.6
    }else if (equal(Term_dom_b,"1")) return "φ^"+i+"_"+fund(a,n)+"("+linePhi(i,a,fund(b,"0"))+"+"+Term.ONE+")"; //3.7
    if (!equal(Term_dom_b,"0")&&!equal(Term_dom_b,"1")) return linePhi(i,a,fund(b,n)); //3.8
  }
  if (S instanceof ChiTerm){ //4
    var k=S.sup;
    var a=S.sub;
    var b=S.inner;
    var dom_b=dom(b);
    var Term_dom_b=new Term(dom_b);
    if (equal(Term_dom_b,"0")||equal(Term_dom_b,"1")) return n+""; //4.1
    else return "χ^"+k+"_"+a+"("+fund(b,n)+")"; //4.2
  }
  if (S instanceof PsiTerm){ //5
    var k=S.sup;
    var a=S.inner;
    var dom_a=dom(a);
    var Term_dom_a=new Term(dom_a);
    var inOT_xk00=inOT("χ^"+k+"_0(0)");
    if (inOT_xk00&&equal(Term_dom_a,"0")) return "χ^"+k+"_"+gamma("0",k,n)+"(0)"; //5.1
    else if (inOT_xk00&&equal(Term_dom_a,"1")) return "χ^"+k+"_"+gamma("0",k,n)+"(ψ^"+k+"("+fund(a,"0")+")+"+Term.ONE+")"; //5.2
    else if (!inOT_xk00&&(equal(Term_dom_a,"0")||equal(Term_dom_a,"1"))){
      var index_k=index(k);
      var Term_index_k=index_k.map(Term);
      if (equal(Term_index_k[1],"0")){
        var j=Term_index_k[0];
        if (equal(dom(j),"1")) return gamma(fund(j,"0"),psiMinus(k,a),n); //5.3
        else return "φ^"+fund(j,n)+"_"+psiMinus(k,a)+"(0)"; //5.4
      }else{ //5.5
        var l=Term_index_k[0];
        var c=Term_index_k[1];
        var dom_c=dom(c);
        var Term_dom_c=new Term(dom_c);
        if (equal(Term_dom_c,"1")){ //5.5.1
          if (equal(dom(n),"1")) return "χ^"+l+"_"+fund(c,"0")+"("+fund(S,fund(n,"0"))+")"; //5.5.1.1
          else return "χ^"+l+"_"+fund(c,"0")+"("+psiMinus(k,a)+")"; //5.5.1.2
        }else if (lessThan("1",Term_dom_c)&&lessThan(Term_dom_c,l)) return "χ^"+l+"_"+fund(c,n)+"("+psiMinus(k,a)+")"; //5.5.2
        else if (lessThanOrEqual(l,Term_dom_c)){ //5.5.3
          if (equal(dom(n),"1")) return "χ^"+l+"_"+fund(c,fund(S,fund(n,"0")))+"(0)"; //5.5.3.1
          else return "χ^"+l+"_"+fund(c,psiMinus(k,a))+"(0)"; //5.5.3.2
        }
      }
    }else if (lessThan(Term_dom_a,k)) return "ψ^"+k+"("+fund(a,n)+")"; //5.6
    else if (lessThanOrEqual(k,Term_dom_a)){ //5.7
      var Term_fund_S_fund_n_0;
      if (equal(dom(n),"1")&&(Term_fund_S_fund_n_0=new Term(fund(S,fund(n,"0")))) instanceof PsiTerm&&equal(Term_fund_S_fund_n_0.sup,k)) return "ψ^"+k+"("+fund(a,"ψ^"+dom_a+"("+Term_fund_S_fund_n_0.inner+")")+")"; //5.7.1
      else return "ψ^"+k+"("+fund(a,"ψ^"+dom_a+"(0)")+")"; //5.7.2
    }
  }
  throw Error("No rule to compute "+S+"["+n+"]");
}
/**
 * @param {Term|string} S 
 */
function inCT(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  return inOT(S)&&lessThan(S,Term.LARGEOMEGA);
}
/**
 * @param {number} n 
 * @returns ⌊n⌋
 */
function fromNumber(n){
  if (n==0) return "0"; //1
  else if (n==1) return Term.ONE+""; //2
  else return (Term.ONE+"+").repeat(n-1)+"+"+Term.ONE; //3
}
/**
 * @param {(Term|string)[]} A 
 * @param {number} n 
 * @returns {number}
 */
function FGH(A,n){
  A=A.map(function(a){return a instanceof Term?a:new Term(a);});
  if (A.length==0) return n; //1
  else{ //2
    var t=A[A.length-1]; //2.1
    var G=A.slice(0,-1); //2.2
    if (equal(t,"0")) return FGH(G,n+1); //2.3
    else{ //2.4
      var Ap=G.concat(Array(n).fill(fund(t,n))); //2.4.1
      return FGH(Ap,n); //2.4.2
    }
  }
}
/**
 * @param {Term|string|number} n 
 * @returns {string} ψ^Ω(⊥(n))
 */
function limitOrd(n){
  if (typeof n=="number") n=String(n);
  if (!(n instanceof Term)) n=new Term(n);
  if (!inOT(n)) throw Error("Invalid argument: "+n);
  var r="φ^0_0(0)";
  while (equal(dom(n),"1")){
    r="φ^"+r+"_0(0)";
    n=pred(n);
  }
  return "ψ^"+Term.LARGEOMEGA+"("+r+")";
}
function calculateN(){
  return FGH([limitOrd(10)],10);
}

var testTerms=[
  "0",
  "1",
  "ω",
  "ω+ω",
  "φ(2)",
  "φ(ω)",
  "φ_1(0)",
  "φ(φ_1(0)+1)",
  "φ_ω(0)",
  "ψ(0)",
  "φ(ψ(0)+1)",
  "φ_ψ(0)(1)",
  "φ_ψ(0)+1(0)",
  "ψ(1)",
  "ψ(Ω)",
  "ψ(Ω+Ω)",
  "ψ(φ(Ω+1))",
  "ψ(φ_1(Ω+1))",
  "ψ(φ_ω(Ω+1))",
  "ψ(φ_Ω(1))",
  "ψ(φ_Ω(2))",
  "ψ(ψ^Ω_2(0))",
  "ψ(Ω_2)",
  "ψ(Ω_2+Ω_2)",
  "ψ(ψ^Ω_3(0))",
  "ψ(Ω_ω)",
  "ψ(Ω_ψ(0))",
  "ψ(Ω_Ω)",
  "ψ(φ^1_1(0))",
  "ψ(ψ^Ω_{φ^1_1(0)+1}(0))",
  "ψ(ψ^Ω_{φ^1_1(0)+1}(ψ^Ω_{φ^1_1(0)+1}(0)))",
  "ψ(Ω_{φ^1_1(0)+1})",
  "ψ(φ^1_1(1))",
  "ψ(φ^1_1(φ^1_1(0)))",
  "ψ(φ^1_2(0))",
  "ψ(φ^1_ω(1))",
  "ψ(ψ^I(0))",
  "ψ(φ^1_ψ^I(0)(1))",
  "ψ(φ^1_ψ^I(0)+1(0))",
  "ψ(ψ^I(1))",
  "ψ(I)",
  "ψ(ψ^Ω_{I+1}(0))",
  "ψ(φ^1_1(I+1))",
  "ψ(φ^1_I(1))",
  "ψ(φ^1_I+1(0))",
  "ψ(ψ^I_1(0))",
  "ψ(I_ω)",
  "ψ(I_ψ(0))",
  "ψ(ψ^χ_1(0)(0))",
  "ψ(ψ^Ω_{ψ^χ_1(0)(0)+1}(0))",
  "ψ(ψ^I_{ψ^χ_1(0)(0)+1}(0))",
  "ψ(ψ^χ_1(0)(1))",
  "ψ(χ_1(0))",
  "ψ(ψ^χ_ω(0)(0))",
  "ψ(ψ^χ_ω(0)(1))",
  "ψ(χ_ω(0))",
  "ψ(ψ^Ω_{χ_ω(0)+1}(0))",
  "ψ(ψ^χ_ω(1)(0))",
  "ψ(ψ^χ_ω+1(0)(0))",
  "ψ(ψ^χ_Ω(0)(0))",
  "ψ(ψ^χ_M(0)(0))",
  "ψ(ψ^χ_M(0)(1))",
  "ψ(χ_M(0))",
  "ψ(ψ^χ_χ_M(0)(0)(0))",
  "ψ(ψ^χ_χ_M(0)(0)(1))",
  "ψ(ψ^χ_χ_M(0)(1)(0))",
  "ψ(ψ^χ_{χ_M(0)+1}(0)(0))",
  "ψ(ψ^χ_M(1)(0))",
  "ψ(ψ^χ_{M+1}(0)(0))",
  "ψ(ψ^χ_{M+M}(0)(0))",
  "ψ(ψ^χ_φ_0(M+1)(0)(0))",
  "ψ(ψ^χ_φ_M(1)(0)(0))",
  "ψ(ψ^M(0))",
  "ψ(ψ^χ_ψ^M(0)(0)(0))",
  "ψ(ψ^χ_{ψ^M(0)+1}(0)(0))",
  "ψ(ψ^χ_M(ψ^M(0)+1)(0))",
  "ψ(ψ^M(1))",
  "ψ(M)",
  "ψ(M+ψ^M(M+1))",
  "ψ(M+M)",
  "ψ(φ(M+1))",
  "ψ(φ_M(1))",
  "ψ(φ_{M+1}(0))",
  "ψ(ψ^Ω_{M+1}(0))",
  "ψ(φ^1_1(M+1))",
  "ψ(φ^1_M(1))",
  "ψ(ψ^χ^{M_1}_0(0)(0))",
  "ψ(ψ^χ^{M_1}_0(1)(0))",
  "ψ(χ^{M_1}_0(ψ(0)))",
  "ψ(χ^{M_1}_0(M))",
  "ψ(ψ^χ^{M_1}_1(0)(0))",
  "ψ(ψ^χ^{M_1}_M(0)(0))",
  "ψ(ψ^χ^{M_1}_M_1(0)(0))",
  "ψ(ψ^χ^{M_1}_M_1(0)(1))",
  "ψ(ψ^χ^{M_1}_χ^{M_1}_M_1(0)(0)(0))",
  "ψ(ψ^χ^{M_1}_M_1(1)(0))",
  "ψ(ψ^M_1(0))",
  "ψ(M_1)",
  "ψ(M_ω)",
  "ψ(φ^2_1(0))",
  "ψ(ψ^χ^χ^{K}_0(0)_0(0)(0))",
  "ψ(ψ^χ^χ^{K}_0(0)_0(0)(1))",
  "ψ(ψ^χ^χ^{K}_0(0)_0(1)(0))",
  "ψ(ψ^χ^χ^{K}_0(0)_1(0)(0))",
  "ψ(ψ^χ^χ^{K}_0(0)_χ^{K}_0(0)(0)(0))",
  "ψ(ψ^χ^χ^{K}_0(0)_χ^χ^{K}_0(0)_χ^{K}_0(0)(0)(0)(0))",
  "ψ(ψ^χ^χ^{K}_0(0)_{χ^{K}_0(0)+1}(0)(0))",
  "ψ(ψ^χ^{K}_0(0)(0))",
  "ψ(ψ^χ^χ^{K}_0(1)_0(0)(0))",
  "ψ(ψ^χ^{K}_0(1)(0))",
  "ψ(ψ^χ^χ^{K}_1(0)_0(0)(0))",
  "ψ(ψ^χ^{K}_1(0)(0))",
  "ψ(ψ^χ^χ^{K}_K(0)_0(0)(0))",
  "ψ(ψ^χ^χ^{K}_ψ^χ^χ^{K}_K(0)_0(0)(0)(0)_0(0)(0))",
  "ψ(ψ^χ^χ^{K}_K(0)_χ^{K}_K(0)(0)(0))",
  "ψ(ψ^χ^{K}_K(0)(0))",
  "ψ(ψ^χ^χ^{K}_ψ^χ^χ^{K}_K(0)_0(0)(0)(χ^{K}_K(0)+1)_0(0)(0))",
  "ψ(ψ^χ^χ^{K}_χ^χ^{K}_K(0)_0(0)(0)_0(0)(0))",
  "ψ(ψ^χ^{K}_χ^χ^{K}_K(0)_0(0)(0)(0))",
  "ψ(ψ^χ^χ^{K}_χ^{K}_K(0)(0)_0(0)(0))",
  "ψ(ψ^χ^{K}_χ^{K}_K(0)(0)(0))",
  "ψ(ψ^χ^χ^{K}_K(1)_0(0)(0))",
  "ψ(ψ^χ^χ^{K}_{K+1}(0)_0(0)(0))",
  "ψ(ψ^K(0))",
  "ψ(K)",
  "ψ(ψ^Ω_{K+1}(0))",
  "ψ(ψ^χ^{M_{K+1}}_0(0)(0))",
  "ψ(ψ^χ^χ^{K_1}_0(0)_0(0)(0))",
  "ψ(K_ω)",
  "ψ(φ^3_1(0))",
  "ψ(ψ^χ^χ^χ^φ^4_0(0)_0(0)_0(0)_0(0)(0))",
  "ψ(ψ^χ^χ^φ^4_0(0)_0(0)_0(0)(0))",
  "ψ(ψ^χ^φ^4_0(0)_0(0)(0))",
  "ψ(ψ^φ^4_0(0)(0))",
  "ψ(φ^4_0(0))",
  "ψ(ψ^φ^ω_0(0)(0))",
  "ψ(ψ^Ω_{ψ^φ^ω_0(0)(0)+1}(1))",
  "ψ(ψ^χ^{M_{ψ^φ^ω_0(0)(0)+1}}_0(0)(0))",
  "ψ(ψ^M_{ψ^φ^ω_0(0)(0)+1}(0))",
  "ψ(ψ^φ^ω_0(0)(1))",
  "ψ(φ^ω_0(0))",
  "ψ(ψ^φ^ω_0(1)(0))",
  "ψ(φ^ω_1(1))",
  "ψ(ψ^χ^φ^{ω+1}_0(0)_0(0)(0))",
  "ψ(ψ^χ^φ^{ω+1}_0(0)_0(0)(1))",
  "ψ(ψ^Ω_{χ^φ^{ω+1}_0(0)_0(0)+1}(0))",
  "ψ(ψ^χ^{M_{χ^φ^{ω+1}_0(0)_0(0)+1}}_0(0)(0))",
  "ψ(ψ^χ^φ^{ω+1}_0(0)_0(1)(0))",
  "ψ(ψ^χ^φ^{ω+1}_0(0)_1(0)(0))",
  "ψ(ψ^χ^φ^{ω+1}_0(1)_0(0)(0))",
  "ψ(φ^{ω+1}_1(0))",
  "ψ(ψ^φ^{Ω}_0(0)(0))",
  "ψ(φ^{Ω}_0(0))",
  "ψ(ψ^φ^{I}_0(0)(0))",
  "ψ(ψ^φ^{M}_0(0)(0))",
  "ψ(ψ^φ^ψ^φ^ω_0(0)(0)_0(0)(0))",
  "ψ(ψ^φ^φ^ω_0(0)_0(0)(0))",
  "ψ(ψ^φ^φ^φ^ω_0(0)_0(0)_0(0)(0))"
];
/** @param {boolean} logInfoToConsole */
function testFunction(logInfoToConsole){
  var r={lessThan:[],inOT:[],errors:[]};
  for (var i=0;i<testTerms.length;i++){
    for (var j=0;j<testTerms.length;j++){
      if (logInfoToConsole) console.log("%cTesting: lessThan, "+testTerms[i]+", "+testTerms[j]+".","color:gold");
      var d=Date.now();
      var caught=false;
      var result;
      try{
        result=lessThan(testTerms[i],testTerms[j]);
      }catch(e){
        var diff=Date.now()-d;
        r.lessThan.push({arg0:testTerms[i],arg1:testTerms[j],result:e,time:diff});
        r.errors.push({test:"lessThan",arg0:testTerms[i],arg1:testTerms[j],name:"error",content:e});
        console.error(e);
        var caught=true;
      }finally{
        var diff=Date.now()-d;
        if (!caught){
          r.lessThan.push({arg0:testTerms[i],arg1:testTerms[j],result:result,time:diff});
          if (logInfoToConsole) console.log(diff);
          if (result!=(i<j)){
            r.errors.push({test:"lessThan",arg0:testTerms[i],arg1:testTerms[j],name:"fail"});
            console.error("Failed test: lessThan, "+testTerms[i]+", "+testTerms[j]+", expected "+(i<j)+".");
          }
        }
      }
    }
  }
  for (var i=0;i<testTerms.length;i++){
    if (logInfoToConsole) console.log("%cTesting: inOT, "+testTerms[i]+".","color:gold");
    var d=Date.now();
    var caught=false;
    var result;
    try{
      result=inOT(testTerms[i]);
    }catch(e){
      var diff=Date.now()-d;
      r.inOT.push({arg0:testTerms[i],result:e,time:diff});
      r.errors.push({test:"inOT",arg0:testTerms[i],name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.inOT.push({arg0:testTerms[i],result:result,time:diff});
        if (logInfoToConsole) console.log(diff);
        if (!result){
          r.errors.push({test:"inOT",arg0:testTerms[i],name:"fail"});
          console.error("Failed test: inOT, "+testTerms[i]+".");
        }
      }
    }
  }
  return r;
}
function JSONStringifyWithError(obj){
  return JSON.stringify(obj,function replaceErrors(key,value){
    if (value instanceof Error){
      var error={};
      Object.getOwnPropertyNames(value).forEach(function (key){error[key]=value[key];});
      return error;
    }
    else return value;
  });
}
function downloadFile(data,filename,type){
  var file=new Blob([data],{type:type});
  var a=document.createElement("a");
  var url=URL.createObjectURL(file);
  a.href=url;
  a.download=filename;
  document.body.appendChild(a);
  a.click();
  setTimeout(function(){
    document.body.removeChild(a);
    window.URL.revokeObjectURL(url);  
  },0); 
}

var input="";
var options={
  abbreviate:undefined,
  detail:undefined
}
var optionList=[
  "abbreviate",
  "detail"
];
var abbreviateOptionList=[
  "1",
  "n",
  "ω",
  "Ω",
  "Ω_n",
  "Ω_ω",
  "Ω_t",
  "I",
  "I_t",
  "M",
  "M_t",
  "K",
  "K_t",
  "2φ",
  "1φ",
  "2χ",
  "1χ",
  "1ψ"
];
function toggleOptions(){
  document.getElementById("options").style.display=document.getElementById("options").style.display=="none"?"block":"none";
}
var last=null;
function compute(){
  var inputChanged=false;
  var oldinput=input;
  inputChanged||=input!=document.getElementById("input").value;
  input=document.getElementById("input").value;
  inputChanged||=!!options.abbreviate!=document.getElementById("abbreviate").checked;
  options.abbreviate=document.getElementById("abbreviate").checked&&(options.abbreviate||{});
  inputChanged||=options.detail!=document.getElementById("detail").checked;
  options.detail=document.getElementById("detail").checked;
  if (options.abbreviate){
    abbreviateOptionList.forEach(function(option){
      var elem=document.getElementById("abbreviate"+option);
      inputChanged||=options.abbreviate[option]!=elem.checked;
      options.abbreviate[option]=elem.checked;
    });
  }
  if (!inputChanged) return;
  if (oldinput!=input) last=[];
  var output="";
  var lines=input.split(lineBreakRegex);
  function abbreviateIfEnabled(x){
    if (options.abbreviate) return abbreviate(x,options.abbreviate);
    else return normalizeAbbreviations(x);
  }
  for (var l=0;l<lines.length;l++){
    var line=lines[l];
    var args=line.split(itemSeparatorRegex);
    var cmd=args.shift();
    output+=line+"\n";
    var result;
    if (oldinput!=input){
      try{
        if (cmd=="normalize"||cmd=="norm"){
          result=normalizeAbbreviations(args[0]);
        }else if (cmd=="abbreviate"||cmd=="abbr"){
          result=null;
        }else if (cmd=="inT"){
          result=inT(args[0]);
        }else if (cmd=="inPT"){
          result=inPT(args[0]);
        }else if (cmd=="inST"){
          result=inST(args[0]);
        }else if (cmd=="inRT"){
          result=inRT(args[0]);
        }else if (cmd=="pred"){
          result=pred(args[0]);
        }else if (cmd=="deg"){
          result=deg(args[0]);
        }else if (cmd=="index"){
          result=index(args[0]);
        }else if (cmd=="termPlus"||cmd=="^+"){
          result=termPlus(args[0]);
        }else if (cmd=="termBullet"){
          result=termBullet(args[0],args[1]);
        }else if (cmd=="lessThanOrEqual"||cmd=="<="){
          result=lessThanOrEqual(args[0],args[1]);
        }else if (cmd=="lessThan"||cmd=="<"){
          result=lessThan(args[0],args[1]);
        }else if (cmd=="triangleLessThan"||cmd=="<|"||cmd=="◁"){
          result=triangleLessThan(args[0],args[1],args[2]);
        }else if (cmd=="inOT"){
          result=inOT(args[0]);
        }else if (cmd=="termAstGeq"||cmd=="^*≥"||cmd=="^*>="){
          result=termAstGeq(args[0],args[1]);
        }else if (cmd=="termMinus"||cmd=="^-"){
          result=termMinus(args[0]);
        }else if (cmd=="dom"){
          result=dom(args[0]);
        }else if (cmd=="gamma"){
          result=gamma(args[0],args[1],args[2]);
        }else if (cmd=="linePhi"){
          result=linePhi(args[0],args[1],args[2]);
        }else if (cmd=="psiMinus"){
          result=psiMinus(args[0],args[1]);
        }else if (cmd=="fund"||cmd=="expand"){
          var t=normalizeAbbreviations(args[0]);
          result=[t];
          for (var i=1;i<args.length;i++){
            result.push(t=fund(t,args[i]));
          }
        }else if (cmd=="inCT"){
          result=inCT(args[0]);
        }else{
          result=null;
        }
      }catch(e){
        result=e;
        console.error(e);
      }
      last[l]=result;
    }else result=last[l];
    if (result instanceof Error){
      output+=result.stack?result.stack:result;
    }else if (cmd=="normalize"||cmd=="norm"){
      output+=result;
    }else if (cmd=="abbreviate"||cmd=="abbr"){
      output+=abbreviate(args[0],options.abbreviate||true);
    }else if (cmd=="inT"){
      output+=result;
    }else if (cmd=="inPT"){
      output+=result;
    }else if (cmd=="inST"){
      output+=result;
    }else if (cmd=="inRT"){
      output+=result;
    }else if (cmd=="pred"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="deg"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="index"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="termPlus"||cmd=="^+"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="termBullet"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="lessThanOrEqual"||cmd=="<="){
      output+=result;
    }else if (cmd=="lessThan"||cmd=="<"){
      output+=result;
    }else if (cmd=="triangleLessThan"||cmd=="<|"||cmd=="◁"){
      output+=result;
    }else if (cmd=="inOT"){
      output+=result;
    }else if (cmd=="termAstGeq"||cmd=="^*≥"||cmd=="^*>="){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="termMinus"||cmd=="^-"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="dom"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="gamma"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="linePhi"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="psiMinus"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="fund"||cmd=="expand"){
      if (options.detail){
        for (var i=1;i<result.length;i++){
          output+=abbreviateIfEnabled(result[i-1])+"["+args[i]+"]="+abbreviateIfEnabled(result[i])+(i==result.length-1?"":"\n");
        }
      }else{
        output+=abbreviateIfEnabled(result[result.length-1]);
      }
    }else if (cmd=="inCT"){
      output+=result;
    }else{
      output+="Unknown command "+cmd;
    }
    output+="\n\n";
  }
  document.getElementById("output").value=output;
}
var handlekey=function(e){}
//console.log=function (s){alert(s)};
window.onerror=function (e,s,l,c,o){alert(JSON.stringify(e+"\n"+s+":"+l+":"+c+"\n"+(o&&o.stack)))};