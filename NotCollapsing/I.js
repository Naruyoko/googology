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
  var PSITERMSUBSCRIPT=1;
  var PSITERMINNER=2;
  var BRACES=3;
  var contextNames=["TOP","PSITERMSUBSCRIPT","PSITERMINNER","BRACES"];
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
    }else if (next=="I"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(ITerm.build());
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
          appendToRSum(PsiTerm.buildNoClone(Term.I.clone(),SumTerm.buildNoClone(decomposed)));
        }
      }else{
        appendToRSum(Term.LARGEOMEGA.clone());
      }
    }else if (next=="+"){
      if (state==CLOSEDTERM){
        state=PLUS;
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (next=="ψ"||next=="p"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var nextnext=scanner.next();
      if (nextnext=="_"){
        var subscriptterm=Term.build(scanner,PSITERMSUBSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var innerterm=Term.build(scanner,PSITERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PsiTerm.buildNoClone(subscriptterm,innerterm));
      }else if (nextnext=="("){
        var innerterm=Term.build(scanner,PSITERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(PsiTerm.buildNoClone(Term.LARGEOMEGA.clone(),innerterm));
      }else throw Error("Expected _ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
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
    }else if (peek=="("&&context==PSITERMSUBSCRIPT){
      state=EXIT;
    }else if (peek==")"&&context==PSITERMINNER){
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
 * @returns {ITerm}
 */
function ITerm(s){
  if (s instanceof ITerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof ITerm)) return new ITerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof ITerm)) throw Error("Invalid expression: "+s);
}
Object.assign(ITerm,Term);
ITerm.build=function (){
  var r=new ITerm();
  return r;
}
ITerm.buildNoClone=function (){
  var r=new ITerm();
  return r;
}
ITerm.prototype=Object.create(Term.prototype);
ITerm.prototype.clone=function (){
  return ITerm.build();
}
/** @param {boolean} abbreviate */
ITerm.prototype.toString=function (abbreviate){
  return "I";
}
ITerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof ITerm;
}
Object.defineProperty(ITerm.prototype,"constructor",{
  value:ITerm,
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
  this.sub=null;
  /** @type {Term} */
  this.inner=null;
}
Object.assign(PsiTerm,Term);
PsiTerm.build=function (sub,inner){
  var r=new PsiTerm();
  r.sub=new Term(sub);
  r.inner=new Term(inner);
  return r;
}
/**
 * @param {Term} sub 
 * @param {Term} inner 
 * @returns {PsiTerm}
 */
PsiTerm.buildNoClone=function (sub,inner){
  var r=new PsiTerm();
  r.sub=sub;
  r.inner=inner;
  return r;
}
PsiTerm.prototype=Object.create(Term.prototype);
PsiTerm.prototype.clone=function (){
  return PsiTerm.build(this.sub,this.inner);
}
/** @param {boolean} abbreviate */
PsiTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1"])&&this.equal(Term.ONE)) return "1";
    else if ((abbreviate===true||abbreviate["ω"])&&this.equal(Term.SMALLOMEGA)) return "ω";
    else if ((abbreviate===true||abbreviate["Ω_1"])&&this.equal(Term.LARGEOMEGA)) return abbreviate===true||abbreviate["Ω"]?"Ω":"Ω_1";
    else if ((abbreviate===true||abbreviate["Ω_n"])&&this.sub.equal(Term.I)&&isNat(this.inner)) return "Ω_"+(toNat(this.inner)+1);
    if ((abbreviate===true||abbreviate["1ψ"])&&this.sub.equal(Term.LARGEOMEGA)) return "ψ("+this.inner.toString(abbreviate)+")";
  }
  return "ψ_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
}
PsiTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof PsiTerm&&this.sub.equal(other.sub)&&this.inner.equal(other.inner);
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
Term.I=new Term("I");
Term.LARGEOMEGA=new Term("ψ_I(0)");
Term.ONE=new Term("ψ_Ω(0)");
Term.SMALLOMEGA=new Term("ψ_Ω(1)");

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
  if (t instanceof ITerm) return true;
  if (t instanceof PsiTerm){
    if ((t.sub instanceof ITerm)&&inT(t.inner)) return true;
    if ((t.sub instanceof PsiTerm)&&(t.sub.sub instanceof ITerm)&&inT(t.sub.inner)&&inT(t.inner)) return true;
    return false;
  }
  if (t instanceof SumTerm) return t.terms.every(inT);
  return false;
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
  if (X instanceof ITerm) return Y instanceof SumTerm&&Y.getLeft() instanceof ITerm;
  if (X instanceof PsiTerm){
    if (Y instanceof ZeroTerm) return false;
    if (Y instanceof ITerm) return true;
    if (Y instanceof PsiTerm){
      if (X.sub instanceof ITerm){
        if (Y.sub instanceof ITerm) return lessThan(X.inner,Y.inner);
        else return lessThan(X,Y.sub);
      }else{
        if (Y.sub instanceof ITerm) return lessThanOrEqual(X.sub,Y);
        else{
          if (equal(X.sub,Y.sub)) return lessThan(X.inner,Y.inner);
          else return lessThan(X.sub,Y.sub);
        }
      }
    }
    if (Y instanceof SumTerm) return lessThanOrEqual(X,Y.getLeft());
  }
  if (X instanceof SumTerm){
    var X_getLeft=X.getLeft();
    if (Y instanceof SumTerm){
      var Y_getLeft=Y.getLeft();
      if (equal(X_getLeft,Y_getLeft)) return lessThan(X.getNotLeft(),Y.getNotLeft());
      else return lessThan(X_getLeft,Y_getLeft);
    }else return lessThan(X_getLeft,Y);
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
 * @returns {string}
 */
function dom(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!inT(X)) throw Error("Invalid argument: "+X);
  if (X instanceof ZeroTerm) return "0";
  if (X instanceof ITerm) return "I";
  if (X instanceof PsiTerm){
    if (X.sub instanceof ITerm) return X+"";
    else if (X.sub instanceof PsiTerm){
      var dom_X_inner=dom(X.inner);
      var Term_dom_X_inner=new Term(dom_X_inner);
      if (equal(Term_dom_X_inner,"0")){
        if (equal(dom(X.sub.inner),"0")) return Term.ONE+"";
        else if (equal(dom(X.sub.inner),"1")) return "ψ_I("+fund(X.sub.inner,"0")+")";
        else return dom(X.sub.inner);
      }else if (equal(Term_dom_X_inner,"1")){
        return Term.SMALLOMEGA+"";
      }else if (equal(Term_dom_X_inner,"ω")){
        return Term.SMALLOMEGA+"";
      }else{
        if (lessThan(Term_dom_X_inner,X)) return dom_X_inner;
        else return Term.SMALLOMEGA+"";
      }
    }
  }
  if (X instanceof SumTerm) return dom(X.getRight());
  throw Error("No rule to compute dom of "+X);
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
    for (var i=0;i<n;i++) a.push(X.clone());
    return SumTerm.build(a);
  }
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
  if (X instanceof ITerm) return Y+"";
  if (X instanceof PsiTerm){
    if (X.sub instanceof ITerm) return Y+"";
    else if (X.sub instanceof PsiTerm){
      var dom_X_inner=dom(X.inner);
      var Term_dom_X_inner=new Term(dom_X_inner);
      if (equal(Term_dom_X_inner,"0")){
        var dom_X_sub_inner=dom(X.sub.inner);
        var Term_dom_X_sub_inner=new Term(dom_X_sub_inner);
        if (equal(Term_dom_X_sub_inner,"0")) return "0";
        else if (equal(Term_dom_X_sub_inner,"1")) return Y+"";
        else return "ψ_I("+fund(X.sub.inner,Y)+")";
      }else if (equal(Term_dom_X_inner,"1")){
        if (isNat(Y)){
          if (equal(X.inner,"1")){
            if (equal(dom(X.sub.inner),"1")) return mult("ψ_I("+fund(X.sub.inner,"0")+")",toNat(Y))+"";
            else return mult("ψ_"+X.sub+"(0)",toNat(Y))+"";
          }else return mult("ψ_"+X.sub+"("+fund(X.inner,"0")+")",toNat(Y))+"";
        }else return "0";
      }else if (equal(Term_dom_X_inner,"ω")){
        return "ψ_"+X.sub+"("+fund(X.inner,Y)+")";
      }else{
        if (lessThan(Term_dom_X_inner,X)) return "ψ_"+X.sub+"("+fund(X.inner,Y)+")";
        else{
          var Z=Term_dom_X_inner;
          var G;
          if (isNat(Y)&&(G=new Term(fund(X,fund(Y,"0")))) instanceof PsiTerm){
            return "ψ_"+X.sub+"("+fund(X.inner,"ψ_"+Z+"("+G.inner+")")+")";
          }else{
            if (Z instanceof PsiTerm&&equal(dom(Z.inner),"1")){
              return "ψ_"+X.sub+"("+fund(X.inner,"ψ_I("+fund(Z.inner,"0")+")")+")";
            }else return "ψ_"+X.sub+"("+fund(X.inner,"ψ_"+Z+"(0)")+")";
          }
        }
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
  return "ψ("+mult("I",n)+")";
}
/**
 * @param {Term|string} X 
 * @param {number} n
 * @returns {number}
 */
function FGH(X,n){
  if (!(X instanceof Term)) X=new Term(X);
  if (!isStandard(X)||(typeof n!="number")) throw Error("Invalid argument: "+X);
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
/*「崩壊しないI関数数」をNumber型が任意の自然数を取り、String型が任意の有限の長さを取り、Arrayが任意の有限の長さを取り、十分な大きさのメモリとスタックが確保されているとき、calculateN()が出力する自然数と定義する。*/

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