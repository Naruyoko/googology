var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ,]/g;
window.onload=function (){
  console.clear();
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
    else if (state==PLUS){
      if (term instanceof ZeroTerm){}
      else if (r instanceof ZeroTerm) r=term;
      else r=SumTerm.buildNoClone([r,term]);
    }else throw Error("Wrong state when attempting to append as sum");
    state=CLOSEDTERM;
  }
  var nums="0123456789";
  var scanner;
  if (typeof s=="string") scanner=new Scanner(s);
  else if (s instanceof Scanner) scanner=s;
  else throw Error("Invalid expression: "+s);
  /** @type {Term} */
  var r=null;
  var startpos=scanner.pos;
  var TOP=0;
  var PSITERMSUPERSCRIPT=1;
  var PSITERMSUBSCRIPT=2;
  var PSITERMINNER=3;
  var IITERMINER=4;
  var BRACES=5;
  var contextNames=["TOP","PSITERMSUPERSCRIPT","PSITERMSUBSCRIPT","PSITERMINNER","IITERMINER","BRACES"];
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
    if (nums.indexOf(next)!=-1){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      scanner.move(-1);
      var num=scanner.nextNumber();
      if (num==0){
        appendToRSum(ZeroTerm.build());
      }else if (num==1){
        appendToRSum(Term.ONE.clone());
      }else{
        var decomposed;
        if (state==START) decomposed=[];
        else if (state==PLUS) decomposed=[r];
        for (var i=0;i<num;i++){
          decomposed.push(Term.ONE.clone());
        }
        r=SumTerm.buildNoClone(decomposed);
        state=CLOSEDTERM;
      }
    }else if (next=="ℐ"||next=="I"&&scanner.peek()=="I"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (next=="I") scanner.move(1);
      var nextnext=scanner.next();
      if (nextnext!="[") throw Error("Expected opening [ at position "+scanner.pos+", instead got "+nextnext+" in expression "+scanner.s);
      var innerterm=Term.build(scanner,IITERMINER);
      var nextnext=scanner.next();
      if (nextnext!="]") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      appendToRSum(IITerm.build(innerterm));
    }else if (next=="ω"||next=="w"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(Term.SMALLOMEGA.clone());
    }else if (next=="Ω"||next=="W"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (scanner.hasNext()&&scanner.peek()=="_"&&nums.indexOf(scanner.peek(1,1))!=-1){
        scanner.move(1);
        var num=scanner.nextNumber();
        if (num==0){
          throw Error("Invalid expression "+scanner.s.substring(scanpos,scanner.pos)+" at position "+scanpos+" in expression "+scanner.s);
        }else if (num==1){
          appendToRSum(Term.LARGEOMEGA.clone());
        }else{
          var decomposed=[];
          for (var i=0;i<num-1;i++){
            decomposed.push(Term.ONE.clone());
          }
          appendToRSum(PsiTerm.buildNoClone(Term.ONE.clone(),Term.I.clone(),SumTerm.buildNoClone(decomposed)));
        }
      }else{
        appendToRSum(Term.LARGEOMEGA.clone());
      }
    }else if (next=="I"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (scanner.hasNext()&&scanner.peek()=="_"&&nums.indexOf(scanner.peek(1,1))!=-1){
        scanner.move(1);
        var num=scanner.nextNumber();
        if (num==0){
          throw Error("Invalid expression "+scanner.s.substring(scanpos,scanner.pos)+" at position "+scanpos+" in expression "+scanner.s);
        }else if (num==1){
          appendToRSum(Term.I.clone());
        }else{
          var decomposed=[];
          for (var i=0;i<num-1;i++){
            decomposed.push(Term.ONE.clone());
          }
          appendToRSum(PsiTerm.buildNoClone(SumTerm.buildNoClone([Term.ONE.clone(),Term.ONE.clone()]),IITerm.buildNoClone(SumTerm.buildNoClone([Term.ONE.clone(),Term.ONE.clone()])),SumTerm.buildNoClone(decomposed)));
        }
      }else{
        appendToRSum(Term.I.clone());
      }
    }else if (next=="+"){
      if (state==CLOSEDTERM){
        state=PLUS;
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (next=="ψ"||next=="p"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var nextnext=scanner.next();
      if (nextnext=="^"){
        var superscriptterm=Term.build(scanner,PSITERMSUPERSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="_") throw Error("Expected _ at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var subscriptterm=Term.build(scanner,PSITERMSUBSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var innerterm=Term.build(scanner,PSITERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PsiTerm.buildNoClone(superscriptterm,subscriptterm,innerterm));
      }else if (nextnext=="("){
        var innerterm=Term.build(scanner,PSITERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PsiTerm.buildNoClone(ZeroTerm.build(),Term.LARGEOMEGA.clone(),innerterm));
      }else throw Error("Expected ^ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
    }else if (next=="{"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character { at position "+scanpos+" in expression "+scanner.s);
      var subterm=Term.build(scanner,BRACES);
      var nextnext=scanner.next();
      if (nextnext!="}") throw Error("Expected closing } at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      if (state==START){
        r=subterm;
        state=CLOSEDTERM;
      }else if (state==PLUS){
        r=SumTerm.buildNoClone([r,subterm]);
        state=CLOSEDTERM;
      }
    }else{
      throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
    }
    var peek=scanner.peek();
    if (peek=="}"&&context==BRACES){
      state=EXIT;
    }else if (peek=="_"&&context==PSITERMSUPERSCRIPT){
      state=EXIT;
    }else if (peek=="("&&context==PSITERMSUBSCRIPT){
      state=EXIT;
    }else if (peek==")"&&context==PSITERMINNER){
      state=EXIT;
    }else if (peek=="]"&&context==IITERMINER){
      state=EXIT;
    }
  }
  if (context==TOP){
    if (scanner.hasNext()) throw Error("Something went wrong");
    if (state==START) r=ZeroTerm.build();
    else if (state==PLUS) throw Error("Unexpected end of input");
    else if (state==CLOSEDTERM){}
  }else{
    if (!scanner.hasNext()) throw Error("Unexpected end of input");
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
 * @returns {IITerm}
 */
function IITerm(s){
  if (s instanceof IITerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof IITerm)) return new IITerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof IITerm)) throw Error("Invalid expression: "+s);
  /** @type {Term} */
  this.inner=null;
}
Object.assign(IITerm,Term);
IITerm.build=function (inner){
  var r=new IITerm();
  r.inner=new Term(inner);
  return r;
}
/**
 * @param {Term} inner 
 * @returns {IITerm}
 */
IITerm.buildNoClone=function (inner){
  var r=new IITerm();
  r.inner=inner;
  return r;
}
IITerm.prototype=Object.create(Term.prototype);
IITerm.prototype.clone=function (){
  return IITerm.build(this.inner);
}
/** @param {boolean} abbreviate */
IITerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["Ω_1"])&&this.equal(Term.LARGEOMEGA)) return abbreviate===true||abbreviate["Ω"]?"Ω":"Ω_1";
    else if ((abbreviate===true||abbreviate["I_1"])&&this.equal(Term.I)) return abbreviate===true||abbreviate["I"]?"I":"I_1";
  }
  return "ℐ["+this.inner.toString(abbreviate)+"]";
}
IITerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof IITerm&&this.inner.equal(other.inner);
}
Object.defineProperty(IITerm.prototype,"constructor",{
  value:IITerm,
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
  this.level=null;
  /** @type {Term} */
  this.sub=null;
  /** @type {Term} */
  this.inner=null;
}
Object.assign(PsiTerm,Term);
PsiTerm.build=function (level,sub,inner){
  var r=new PsiTerm();
  r.level=new Term(level);
  r.sub=new Term(sub);
  r.inner=new Term(inner);
  return r;
}
/**
 * @param {Term} level 
 * @param {Term} sub 
 * @param {Term} inner 
 * @returns {PsiTerm}
 */
PsiTerm.buildNoClone=function (level,sub,inner){
  var r=new PsiTerm();
  r.level=level;
  r.sub=sub;
  r.inner=inner;
  return r;
}
PsiTerm.prototype=Object.create(Term.prototype);
PsiTerm.prototype.clone=function (){
  return PsiTerm.build(this.level,this.sub,this.inner);
}
PsiTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1"])&&this.equal(Term.ONE)) return "1";
    else if ((abbreviate===true||abbreviate["ω"])&&this.equal(Term.SMALLOMEGA)) return "ω";
    else if ((abbreviate===true||abbreviate["Ω_n"])&&this.level.equal(Term.ONE)&&this.sub.equal(Term.I)&&isNat(this.inner)) return "Ω_"+(toNat(this.inner)+1);
    else if ((abbreviate===true||abbreviate["I_n"])&&this.level.equal("2")&&this.sub.equal("ℐ[2]")&&isNat(this.inner)) return "I_"+(toNat(this.inner)+1);
    if ((abbreviate===true||abbreviate["2ψ"])&&this.level.equal(Term.ZERO)){
      if ((abbreviate===true||abbreviate["1ψ"])&&this.sub.equal(Term.LARGEOMEGA)) return "ψ("+this.inner.toString(abbreviate)+")";
      else return "ψ_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
    }
  }
  var superscriptstr=this.level.toStringWithImplicitBrace(abbreviate);
  if (/^[ΩI](_|$)/.test(superscriptstr)) superscriptstr="{"+superscriptstr+"}";
  return "ψ^"+superscriptstr+"_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
}
PsiTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof PsiTerm&&this.level.equal(other.level)&&this.sub.equal(other.sub)&&this.inner.equal(other.inner);
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
Term.LARGEOMEGA=new Term("ℐ[0]");
Term.ONE=new Term("ψ^0_Ω(0)");
Term.SMALLOMEGA=new Term("ψ^0_Ω(1)");
Term.I=new Term("ℐ[1]");

/**
 * @param {Term} t
 * @param {(value:Term,index:number,array:Term[])=>boolean} f
 */
 function isSumAndTermsSatisfy(t,f){
  return t instanceof SumTerm&&t.terms.every(f);
}
/** @returns {boolean} */
function isNat(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  return t.equal("1")||isSumAndTermsSatisfy(t,equalFunc("1"));
}
/** @returns {number} */
function toNat(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return NaN;
  }
  if (isNat(t)){
    if (t instanceof PsiTerm) return 1;
    else return t.terms.length;
  }else return NaN;
}
/** @returns {boolean} */
function inT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return true;
  if (t instanceof IITerm) return inT(t.inner);
  if (t instanceof PsiTerm){
    if (inT(t.level)&&inT(t.sub)&&inT(t.inner)&&lessThan(t.level,regulimity(t.sub))){
      if (t.sub instanceof IITerm) return true;
      if (t.sub instanceof PsiTerm){
        if (t.sub.sub instanceof PsiTerm&&equal(t.sub.inner,"0")&&equal(t.sub.sub.inner,"0")) return false;
        else return true;
      }
      return false;
    }else return false;
  }
  if (t instanceof SumTerm) return t.terms.every(inT);
  return false;
}
/**
 * @param {Term|string} X 
 * @returns {Term}
 */
function regulimity(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (X instanceof ZeroTerm) return ZeroTerm.build();
  if (X instanceof IITerm) return leftSucc(X.inner);
  if (X instanceof PsiTerm){
    if (lessThan(dom(X.inner),X)) return X.level.clone();
    else return ZeroTerm.build();
  }
  if (X instanceof SumTerm) return ZeroTerm.build();
  throw Error("No rule to compute regulimity of "+X);
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
 * @param {Term|string} X 
 * @param {Term|string} Y 
 * @returns {boolean}
 */
function lessThan(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  if (X instanceof ZeroTerm) return !(Y instanceof ZeroTerm);
  if (X instanceof IITerm){
    if (Y instanceof ZeroTerm) return false;
    if (Y instanceof IITerm) return lessThan(X.inner,Y.inner);
    if (Y instanceof PsiTerm) return lessThan(X,Y.sub);
    if (Y instanceof SumTerm) return lessThanOrEqual(X,Y.getLeft());
  }
  if (X instanceof PsiTerm){
    if (Y instanceof ZeroTerm) return false;
    if (Y instanceof IITerm) return !lessThanOrEqual(Y,X);
    if (Y instanceof PsiTerm){
      if (!(X.sub instanceof IITerm||X.sub instanceof PsiTerm)) throw Error("Unexpected error");
      if (!(Y.sub instanceof IITerm||Y.sub instanceof PsiTerm)) throw Error("Unexpected error");
      if (equal(X.sub,Y.sub)){
        if (equal(X.level,Y.level)) return lessThan(X.inner,Y.inner);
        else return lessThan(X.level,Y.level);
      }else{
        if (equal(X.level,Y.level)){
          if (lessThan(dom(X.sub.inner),"ω")){
            if (lessThan(dom(Y.sub.inner),"ω")) return lessThan(X.sub,Y.sub);
            else return lessThan(X.sub,Y);
          }else{
            if (lessThan(dom(Y.sub.inner),"ω")) return lessThan(X,Y.sub);
            else return lessThan(X.sub,Y.sub);
          }
        }else if (lessThan(X.level,Y.level)){
          if (lessThan(dom(X.sub.inner),"ω")) return lessThanOrEqual(X.sub,Y);
          else{
            if (X.sub instanceof IITerm) return lessThan(X,Y.sub);
            if (X.sub instanceof PsiTerm) return lessThanOrEqual(X.sub,Y);
          }
        }else{
          if (lessThan(dom(Y.sub.inner),"ω")) return lessThan(X,Y.sub);
          else{
            if (Y.sub instanceof IITerm) return lessThan(X.sub,Y);
            if (Y.sub instanceof PsiTerm) return lessThan(X,Y.sub);
          }
        }
      }
    }
    if (Y instanceof SumTerm) return lessThanOrEqual(X,Y.getLeft());
  }
  if (X instanceof SumTerm){
    if (Y instanceof SumTerm){
      if (equal(X.getLeft(),Y.getLeft())) return lessThan(X.getNotLeft(),Y.getNotLeft());
      else return lessThan(X.getLeft(),Y.getLeft());
    }else return lessThan(X.getLeft(),Y);
  }
  throw Error("No rule to compare "+X+" and "+Y);
}
/**
 * @param {Term|string} X 
 * @param {Term|string} Y 
 */
function lessThanOrEqual(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  return equal(X,Y)||lessThan(X,Y);
}
/**
 * @param {Term|string} X 
 * @param {Term|string} Y 
 * @returns {boolean}
 */
function isPlusNat(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  if (X instanceof ZeroTerm) return isNat(Y);
  if (X instanceof SumTerm){
    if (Y instanceof SumTerm){
      if (Y.terms.length<=X.terms.length) return false;
      for (var i=0;i<Y.terms.length;i++){
        if (i<X.terms.length){
          if (!equal(X.terms[i],Y.terms[i])) return false;
        }else{
          if (!equal(Y.terms[i],"1")) return false;
        }
      }
      return true;
    }else return false;
  }else{
    if (Y instanceof SumTerm) return equal(X,Y.getLeft())&&isNat(Y.getNotLeft());
    else return false;
  }
}
/**
 * @param {Term|string} X 
 * @returns {Term}
 */
function removeNat(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (X instanceof SumTerm){
    for (var i=X.terms.length-1;i>=0;i--){
      if (!equal(X.terms[i],"1")) return SumTerm.build(X.terms.slice(0,i+1));
    }
    return ZeroTerm.build();
  }else return X.clone();
}
/**
 * @param {Term|string} X 
 * @returns {string}
 */
function dom(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!inT(X)) throw Error("Invalid argument: "+X);
  if (X instanceof ZeroTerm) return "0";
  if (X instanceof IITerm){
    var dom_regulimity_X=dom(regulimity(X));
    var Term_dom_regulimity_X=new Term(dom_regulimity_X);
    if (equal(Term_dom_regulimity_X,"1")) return X+"";
    else return dom_regulimity_X;
  }
  if (X instanceof PsiTerm){
    var dom_X_level=dom(X.level);
    var Term_dom_X_level=new Term(dom_X_level);
    if (equal(Term_dom_X_level,"0")){
      var dom_X_inner=dom(X.inner);
      var Term_dom_X_inner=new Term(dom_X_inner);
      if (equal(Term_dom_X_inner,"0")){
        if (X.sub instanceof IITerm){
          if (lessThan(X.sub.inner,"ω")) return normalizeAbbreviations("1");
          else return dom(removeNat(X.sub.inner));
        }
        if (X.sub instanceof PsiTerm){
          var dom_X_sub_inner=dom(X.sub.inner);
          var Term_dom_X_sub_inner=new Term(dom_X_sub_inner);
          if (equal(X.sub.level,"1")){
            if (equal(Term_dom_X_sub_inner,"1")) return "ψ^"+X.sub.level+"_"+X.sub.sub+"("+fund(X.sub.inner,"0")+")";
            else return dom_X_sub_inner;
          }else if (equal(dom(X.sub.level),"1")){
            if (equal(Term_dom_X_sub_inner,"1")) return dom(X.sub);
            else return dom_X_sub_inner;
          }else{
            if (equal(Term_dom_X_sub_inner,"1")) return dom(X.sub.level);
            else return dom_X_sub_inner;
          }
        }
      }else if (equal(Term_dom_X_inner,"1")){
        return Term.SMALLOMEGA+"";
      }else if (equal(Term_dom_X_inner,"ω")){
        return Term.SMALLOMEGA+"";
      }else{
        if (lessThan(Term_dom_X_inner,X)) return dom_X_inner;
        else return Term.SMALLOMEGA+"";
      }
    }else if (equal(dom_X_level,"1")){
      if (lessThan(dom(X.inner),X)) return X+"";
      else return Term.SMALLOMEGA+"";
    }else{
      if (lessThan(dom(X.inner),X)) return dom_X_level;
      else return Term.SMALLOMEGA+"";
    }
  }
  if (X instanceof SumTerm) return dom(X.getRight());
  throw Error("No rule to compute dom of "+X);
}
/**
 * @param {Term|string} X 
 * @returns {Term}
 */
function leftPred(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (X instanceof ZeroTerm) return ZeroTerm.build();
  else if (isNat(X)) return mult("1",toNat(X)-1);
  else return X.clone();
}
/**
 * @param {Term|string} X 
 * @returns {Term}
 */
function leftSucc(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (X instanceof ZeroTerm) return Term.ONE.clone();
  else if (isNat(X)) return mult("1",toNat(X)+1);
  else return X.clone();
}
/**
 * @param {Term|string} X 
 * @param {number} n 
 * @returns {Term}
 */
function mult(X,n){
  if (!(X instanceof Term)) X=new Term(X);
  if (n==0) return ZeroTerm.build();
  else if (n==1) return X.clone();
  else{
    var a=[];
    var t=X.clone();
    for (var i=0;i<n;i++) a.push(t);
    return SumTerm.build(a);
  }
}
/**
 * @param {Term|string} X 
 * @returns {string}
 */
function fixSubscript(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (X instanceof ZeroTerm) return "0";
  if (X instanceof IITerm) return X+"";
  if (X instanceof PsiTerm){
    if (X.inner instanceof ZeroTerm){
      if (X.sub instanceof IITerm){
        if (equal(X.sub.inner,"0")) return X+"";
        else{
          if (isPlusNat(X.level,regulimity(X.sub))) return "ℐ["+leftPred(X.level)+"]";
          else return "ψ^"+X.level+"_ℐ["+removeNat(X.sub.inner)+"]("+X.inner+")";
        }
      }
      if (X.sub instanceof PsiTerm){
        var dom_X_sub_inner=dom(X.sub.inner);
        var Term_dom_X_sub_inner=new Term(dom_X_sub_inner);
        if (lessThan(Term_dom_X_sub_inner,"ω")){
          if (isPlusNat(X.level,X.sub.level)){
            if (equal(Term_dom_X_sub_inner,"0")) return fixSubscript("ψ^"+X.level+"_"+X.sub.sub+"("+X.sub.inner+")");
            else if (equal(Term_dom_X_sub_inner,"1")) return fixSubscript("ψ^"+X.sub.level+"_"+X.sub.sub+"("+fund(X.sub.inner,"0")+")");
            else return "ψ^"+X.level+"_ψ^"+removeNat(X.sub.level)+"_"+X.sub.sub+"("+X.sub.inner+")("+X.inner+")";
          }else{
            if (equal(Term_dom_X_sub_inner,"0")) return fixSubscript("ψ^"+X.level+"_"+X.sub.sub+"("+X.sub.inner+")");
            else if (equal(Term_dom_X_sub_inner,"1")){
              if (equal(X.level,"0")) return fixSubscript("ψ^"+X.sub.level+"_"+X.sub.sub+"("+fund(X.sub.inner,"0")+")");
              else return X+"";
            }else return "ψ^"+X.level+"_ψ^"+removeNat(X.sub.level)+"_"+X.sub.sub+"("+X.sub.inner+")("+X.inner+")";
          }
        }else return X+"";
      }
    }else{
      if (X.sub instanceof IITerm) return X+"";
      if (X.sub instanceof PsiTerm){
        if (X.sub.inner instanceof ZeroTerm){
          if (isPlusNat(X.sub.level,regulimity(X.sub.sub))) return X+"";
          else return "ψ^"+X.level+"_"+X.sub.sub+"("+X.inner+")";
        }else return X+"";
      }
    }
  }
  throw Error("No rule to fix subscript of "+X);
}
/**
 * @param {Term|string} X 
 * @param {Term|string|number} Y 
 * @returns {string}
 */
function fund(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (typeof Y=="number") Y=String(Y);
  if (!(Y instanceof Term)) Y=new Term(Y);
  if (!inT(X)||!inT(Y)) throw Error("Invalid argument: "+X+","+Y);
  if (X instanceof ZeroTerm) return "0";
  if (X instanceof IITerm){
    var regulimity_X=regulimity(X);
    var Term_regulimity_X=new Term(regulimity_X);
    if (equal(dom(Term_regulimity_X),"1")) return Y+"";
    else return "ψ^"+fund(Term_regulimity_X,Y)+"_"+X+"(0)";
  }
  if (X instanceof PsiTerm){
    var dom_X_inner=dom(X.inner);
    var Term_dom_X_inner=new Term(dom_X_inner);
    if (equal(X.level,"0")){
      if (equal(Term_dom_X_inner,"0")){
        if (X.sub instanceof IITerm){
          if (lessThan(X.sub.inner,"ω")) return "0";
          else return "ℐ["+fund(X.sub.inner,Y)+"]";
        }
        if (X.sub instanceof PsiTerm){
          if (equal(X.sub.level,"1")){
            if (equal(dom(X.sub.inner),"1")) return fixSubscript(X);
            else return fixSubscript("ψ^"+X.sub.level+"_"+X.sub.sub+"("+fund(X.sub.inner,Y)+")");
          }else if (equal(dom(X.sub.level),"1")){
            if (equal(dom(X.sub.inner),"1")) return fixSubscript("ψ^"+X.level+"_"+fund(X.sub,Y)+"("+X.inner+")");
            else return fixSubscript("ψ^"+X.sub.level+"_"+X.sub.sub+"("+fund(X.sub.inner,Y)+")");
          }else{
            if (equal(dom(X.sub.inner),"1")) return fixSubscript("ψ^"+fund(X.sub.level,Y)+"_"+fixSubscript("ψ^"+X.sub.level+"_"+X.sub.sub+"("+fund(X.sub.inner,"0")+")")+"(0)");
            else return fixSubscript("ψ^"+X.sub.level+"_"+X.sub.sub+"("+fund(X.sub.inner,Y)+")");
          }
        }
      }else if (equal(Term_dom_X_inner,"1")){
        if (isNat(Y)) return mult(fixSubscript("ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,"0")+")"),toNat(Y))+"";
        else return "0";
      }else if (equal(Term_dom_X_inner,"ω")){
        return fixSubscript("ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,Y)+")");
      }else{
        if (lessThan(Term_dom_X_inner,X)) return "ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,Y)+")";
        else{
          var Z=Term_dom_X_inner;
          var G;
          if (isNat(Y)&&(G=new Term(fund(X,fund(Y,"0")))) instanceof PsiTerm){
            return "ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,fixSubscript("ψ^"+fund(regulimity(Z),"0")+"_"+Z+"("+G.inner+")"))+")";
          }else return "ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,fixSubscript("ψ^"+fund(regulimity(Z),"0")+"_"+Z+"(0)"))+")";
        }
      }
    }else if (equal(dom(X.level),"1")){
      if (lessThan(Term_dom_X_inner,X)) return Y+"";
      else{
        var Z=Term_dom_X_inner;
        var G;
        if (isNat(Y)&&(G=new Term(fund(X,fund(Y,"0")))) instanceof PsiTerm){
          return "ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,fixSubscript("ψ^"+fund(regulimity(Z),"0")+"_"+Z+"("+G.inner+")"))+")";
        }else return "ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,fixSubscript("ψ^"+fund(regulimity(Z),"0")+"_"+Z+"(0)"))+")";
      }
    }else{
      if (lessThan(Term_dom_X_inner,X)) return fixSubscript("ψ^"+fund(regulimity(X),Y)+"_"+X+"(0)");
      else{
        var Z=Term_dom_X_inner;
        var G;
        if (isNat(Y)&&(G=new Term(fund(X,fund(Y,"0")))) instanceof PsiTerm){
          return "ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,fixSubscript("ψ^"+fund(regulimity(Z),"0")+"_"+Z+"("+G.inner+")"))+")";
        }else return "ψ^"+X.level+"_"+X.sub+"("+fund(X.inner,fixSubscript("ψ^"+fund(regulimity(Z),"0")+"_"+Z+"(0)"))+")";
      }
    }
  }
  if (X instanceof SumTerm){
    var fund_X_getRight_Y=fund(X.getRight(),Y)
    if (equal(fund_X_getRight_Y,"0")) return X.getNotRight()+"";
    else return X.getNotRight()+"+"+fund_X_getRight_Y;
  }
  throw Error("No rule to compute fund of "+X+","+Y);
}
/**
 * @param {Term|string} x 
 * @param {number=} limit 
 * @returns {{isStandard:boolean,path:string[],funds:number[]}}
 */
function findOTPath(x,limit){
  if (!(x instanceof Term)) x=new Term(x);
  if (!inT(x)) throw Error("Invalid argument: "+x);
  if (typeof limit=="undefined"||limit==-1) limit=Infinity;
  if (equal(x,"0")){
    return {isStandard:true,path:["0"],funds:[-1]};
  }else{
    var n=0;
    var t;
    while(n<=limit&&!lessThanOrEqual(x,limitOrd(n))){
      n++;
    };
    if (n>limit) return {isStandard:false,path:[],funds:[]};
    t=limitOrd(n);
    console.log(abbreviate(t));
    var r={isStandard:false,path:[t],funds:[n]};
    while (!equal(x,t)){
      n=0;
      var nt;
      while (n<=limit&&lessThan(nt=fund(t,n),x)) n++;
      if (n>limit) return r;
      r.path.push(t=nt);
      r.funds.push(n);
      console.log(abbreviate(nt));
    }
    r.isStandard=true;
    return r;
  }
}
/**
 * @param {Term|string} x 
 * @param {number=} limit 
 * @returns {boolean}
 */
function isStandard(x,limit){
  return findOTPath(x,limit).isStandard;
}
/** @param {number} n */
function limitOrd(n){
  if (n==0) return normalizeAbbreviations("ψ(0)");
  else return normalizeAbbreviations("ψ("+"ℐ[".repeat(n)+"0"+"]".repeat(n)+")");
}
/**
 * @param {Term|string} X 
 * @param {number} n
 * @returns {number}
 */
function FGH(X,n){
  if (!(X instanceof Term)) X=new Term(X);
  if (!inT(X)||typeof n!="number") throw Error("Invalid argument: "+X+","+n);
  if (equal(dom(X),"0")) return n+1;
  else if (equal(dom(X),"1")){
    var r=n;
    var X0=fund(X,"0");
    for (var i=0;i<n;i++) r=FGH(X0,r);
    return r;
  }else return FGH(fund(X,n),n);
}
/** @param {number} n */
function largeFunction(n){
  if (typeof n!="number") throw Error("Invalid argument");
  return FGH(limitOrd(n),n);
}
function calculateN(){
  var r=1e100;
  for (var i=0;i<1e100;i++) r=largeFunction(r);
  return r;
}
/*「崩壊しないℐ関数数」をNumber型が任意の自然数を取り、String型が任意の有限の長さを取り、Arrayが任意の有限の長さを取り、十分な大きさのメモリとスタックが確保されているとき、calculateN()が出力する自然数と定義する。*/

var testTerms=[
  "ψ(Ω)",
  "ψ(Ω_2)",
  "ψ(Ω_2+Ω_2)",
  "ψ(ψ^0_ψ^1_I(ω)(0))",
  "ψ(ψ^1_I(ω))",
  "ψ(I)",
  "ψ(I+ψ^1_I(I+1))",
  "ψ(ψ^0_ψ^1_I_2(1)(1))",
  "ψ(ψ^1_I_2(1))",
  "ψ(I_2)",
  "ψ(ψ^0_ψ^2_ℐ[2](ω)(0))",
  "ψ(ψ^0_ψ^1_ψ^2_ℐ[2](ω)(0)(1))",
  "ψ(ψ^1_ψ^2_ℐ[2](ω)(0))",
  "ψ(ψ^2_ℐ[2](ω))",
  "ψ(ψ^2_ℐ[2](I))",
  "ψ(ψ^1_ψ^2_ℐ[2](I+1)(1))",
  "ψ(ℐ[2])",
  "ψ(ℐ[2]+ψ^2_ℐ[2](1))",
  "ψ(ℐ[2]+ψ^2_ℐ[2](I))",
  "ψ(ℐ[2]+ψ^1_ψ^2_ℐ[2](I+1)(1))",
  "ψ(ℐ[2]+ψ^2_ℐ[2](I+1))",
  "ψ(ℐ[2]+ψ^2_ℐ[2](ℐ[2]))",
  "ψ(ψ^0_ℐ[ω](0))",
  "ψ(ψ^1_ℐ[ω](0))",
  "ψ(ℐ[ω]+ψ^1_I(ℐ[2]))",
  "ψ(ℐ[ω]+ψ^0_ψ^1_ψ^2_ℐ[2](1)(I)(0))",
  "ψ(ℐ[ω]+ψ^0_ℐ[ω](0))",
  "ψ(ℐ[ω]+ψ^1_ℐ[ω](0))",
  "ψ(ℐ[ω]+ψ^1_ℐ[ω](1))",
  "ψ(ℐ[ω+1]+ψ^0_ψ^ω_ℐ[ω+1](1)(1))",
  "ψ(ℐ[ω+1]+ψ^ω_ℐ[ω+1](1))",
  "ψ(ψ^0_ℐ[ω+ω](0))",
  "ψ(ψ^ω_ℐ[ω+ω](0))",
  "ψ(ψ^0_ψ^ω_ℐ[ω+ω](1)(1))",
  "ψ(ψ^ω_ℐ[ω+ω](1))",
  "ψ(ℐ[ω+ω]+ψ^ω_ℐ[ω+ω](1))",
  "ψ(ℐ[ω+ω]+ψ^ω+2_ℐ[ω+ω](0))",
  "ψ(ψ^0_ℐ[Ω](0))",
  "ψ(ψ^ω_ℐ[Ω](0))",
  "ψ(ℐ[Ω]+ψ^0_ℐ[Ω](0))",
  "ψ(ℐ[Ω]+ψ^ω_ℐ[Ω](0))",
  "ψ(ℐ[ℐ[Ω]])"
];
/** @param {boolean} logInfoToConsole */
function testFunction(logInfoToConsole){
  function f(t,l){var r=findOTPath(t,l||3);console.log(r.isStandard);console.log(r.path.map(abbreviate));return r;}
  var r={lessThan:[],isStandard:[],errors:[]};
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
    if (logInfoToConsole) console.log("%cTesting: isStandard, "+testTerms[i]+".","color:gold");
    var d=Date.now();
    var caught=false;
    var result;
    try{
      result=findOTPath(testTerms[i],3);
    }catch(e){
      var diff=Date.now()-d;
      r.isStandard.push({arg0:testTerms[i],result:e,time:diff});
      r.errors.push({test:"isStandard",arg0:testTerms[i],name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.isStandard.push({arg0:testTerms[i],result:result,time:diff});
        if (logInfoToConsole) console.log(diff);
        if (!result.isStandard){
          r.errors.push({test:"isStandard",arg0:testTerms[i],name:"fail"});
          console.error("Failed test: isStandard, "+testTerms[i]+".");
        }
      }
    }
  }
  return r;
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
  "Ω_1",
  "Ω_n",
  "I",
  "I_1",
  "I_n",
  "2ψ",
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
          result=abbreviate(args[0]);
        }else if (cmd=="inT"){
          result=inT(args[0]);
        }else if (cmd=="regulimity"){
          result=regulimity(args[0]);
        }else if (cmd=="lessThan"||cmd=="<"){
          result=lessThan(args[0],args[1]);
        }else if (cmd=="lessThanOrEqual"||cmd=="<="){
          result=lessThanOrEqual(args[0],args[1]);
        }else if (cmd=="dom"){
          result=dom(args[0]);
        }else if (cmd=="expand"){
          var t=normalizeAbbreviations(args[0]);
          result=[t];
          for (var i=1;i<args.length;i++){
            result.push(t=fund(t,args[i]));
          }
        }else if (cmd=="isStandard"){
          result=findOTPath(args[0],+args[1]||3);
        }else{
          result=null;
        }
      }catch(e){
        result=e;
      }
      last[l]=result;
    }else result=last[l];
    if (result instanceof Error){
      output+=result.stack?result.stack:result;
    }else if (cmd=="normalize"||cmd=="norm"){
      output+=result;
    }else if (cmd=="abbreviate"||cmd=="abbr"){
      output+=result;
    }else if (cmd=="inT"){
      output+=result;
    }else if (cmd=="regulimity"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="lessThan"||cmd=="<"){
      output+=result;
    }else if (cmd=="lessThanOrEqual"||cmd=="<="){
      output+=result;
    }else if (cmd=="dom"){
      output+=result;
    }else if (cmd=="expand"){
      if (options.detail){
        for (var i=1;i<result.length;i++){
          output+=abbreviateIfEnabled(result[i-1])+"["+args[i]+"]="+abbreviateIfEnabled(result[i])+(i==result.length-1?"":"\n");
        }
      }else{
        output+=abbreviateIfEnabled(result[result.length-1]);
      }
    }else if (cmd=="isStandard"){
      if (options.detail){
        for (var i=1;i<result.path.length;i++){
          output+=abbreviateIfEnabled(result.path[i-1])+"["+result.funds[i]+"]="+abbreviateIfEnabled(result.path[i])+"\n";
        }
        if (result.isStandard) output+=abbreviateIfEnabled(args[0])+"∈OT";
        else output+=abbreviateIfEnabled(args[0])+"∉OT limited to n≦"+(+args[1]||3);
      }else{
        output+=result.isStandard;
      }
    }else{
      output+="Unknown command "+cmd;
    }
    output+="\n\n";
  }
  document.getElementById("output").value=output;
}
var handlekey=function(e){}
//console.log=function (s){alert(s)};
window.onerror=function (e,s,l,c,o){alert(JSON.stringify(e+"\n"+s+":"+l+":"+c+"\n"+o.stack))};
