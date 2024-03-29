var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ]/g;
window.onload=function (){
  console.clear();
  setupTestTerms();
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
  var symbols="+(){}_,";
  var notword=nums+symbols;
  var NUMBER=0;
  var SYMBOL=1;
  var WORD=2;
  var symbolTypes=["NUMBER","SYMBOL","WORD"];
  /** @type {Term} */
  var r=null;
  var startpos=scanner.pos;
  var TOP=0;
  var THREETERMSUBSCRIPT=1;
  var THREETERMINNER=2;
  var BRACES=3;
  var contextNames=["TOP","THREETERMSUBSCRIPT","THREETERMINNER","BRACES"];
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
        for (var i=0;i<num;i++){
          decomposed.push(Term.ONE.clone());
        }
        appendToRSum(SumTerm.buildNoClone(decomposed));
        state=CLOSEDTERM;
      }
    }else if (nextWord=="ω"||nextWord=="w"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(Term.SMALLOMEGA.clone());
    }else if (nextWord=="+"){
      if (state==CLOSEDTERM){
        state=PLUS;
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (nextWord=="三"||nextWord=="t"||nextWord=="three"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var nextnext=scanner.next();
      if (nextnext=="_"){
        var subscriptterm=Term.build(scanner,THREETERMSUBSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var inner2term=Term.build(scanner,THREETERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(ThreeTerm.buildNoClone(subscriptterm,inner2term));
      }else if (nextnext=="("){
        var inner1term=Term.build(scanner,THREETERMINNER);
        var nextnext=scanner.next();
        if (nextnext==","){
          var inner2term=Term.build(scanner,THREETERMINNER);
          var nextnext=scanner.next();
          if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
          appendToRSum(ThreeTerm.buildNoClone(inner1term,inner2term));
        }else if (nextnext==")") appendToRSum(ThreeTerm.buildNoClone(ZeroTerm.build(),inner1term));
        else throw Error("Expected closing ) or a comma at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      }else throw Error("Expected _ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
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
      }else if (context==THREETERMSUBSCRIPT&&peek=="("){
        state=EXIT;
      }else if (context==THREETERMINNER&&(peek==","||peek==")")){
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
/** @returns {string} */
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
 * @returns {ThreeTerm}
 */
function ThreeTerm(s){
  if (s instanceof ThreeTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof ThreeTerm)) return new ThreeTerm(s);
  /** @type {ThreeTerm} */
  Term.call(this,s);
  if (s&&!(this instanceof ThreeTerm)) throw Error("Invalid expression: "+s);
  /** @type {Term} */
  this.inner1=null;
  /** @type {Term} */
  this.inner2=null;
}
Object.assign(ThreeTerm,Term);
ThreeTerm.build=function (inner1,inner2){
  var r=new ThreeTerm();
  r.inner1=new Term(inner1);
  r.inner2=new Term(inner2);
  return r;
}
/**
 * @param {Term} inner1 
 * @param {Term} inner2 
 * @returns {ThreeTerm}
 */
ThreeTerm.buildNoClone=function (inner1,inner2){
  var r=new ThreeTerm();
  r.inner1=inner1;
  r.inner2=inner2;
  return r;
}
ThreeTerm.prototype=Object.create(Term.prototype);
ThreeTerm.prototype.clone=function (){
  return ThreeTerm.build(this.inner1,this.inner2);
}
/** @param {boolean} abbreviate */
ThreeTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1"])&&this.equal(Term.ONE)) return "1";
    else if ((abbreviate===true||abbreviate["ω"])&&this.equal(Term.SMALLOMEGA)) return "ω";
    else if ((abbreviate===true||abbreviate["1三"])&&this.inner1.equal(Term.ZERO)) return "三("+this.inner2.toString(abbreviate)+")";
    else if ((abbreviate===true||abbreviate["2三"])) return "三_"+this.inner1.toStringWithImplicitBrace(abbreviate)+"("+this.inner2.toString(abbreviate)+")";
  }
  return "三("+this.inner1.toString(abbreviate)+","+this.inner2.toString(abbreviate)+")";
}
ThreeTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof ThreeTerm&&this.inner1.equal(other.inner1)&&this.inner2.equal(other.inner2);
}
Object.defineProperty(ThreeTerm.prototype,"constructor",{
  value:ThreeTerm,
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
  return this.terms[0];
}
/** @returns {Term} */
SumTerm.prototype.getNotLeft=function (){
  if (this.terms.length<2) return ZeroTerm.build();
  else if (this.terms.length<=2) return this.terms[1];
  else return SumTerm.buildNoClone(this.terms.slice(1));
}
SumTerm.prototype.getRight=function (){
  return this.terms[this.terms.length-1];
}
/** @returns {Term} */
SumTerm.prototype.getNotRight=function (){
  if (this.terms.length<2) return ZeroTerm.build();
  else if (this.terms.length<=2) return this.terms[0];
  else return SumTerm.buildNoClone(this.terms.slice(0,-1));
}
/**
 * @param {number} start 
 * @param {number=} end 
 * @returns {Term}
 */
SumTerm.prototype.slice=function (start,end){
  if (start<0) start=this.terms.length+start;
  if (end===undefined) end=this.terms.length;
  if (end<0) end=this.terms.length+end;
  if (start>=end) return NullTerm.build();
  else if (end-start==1) return this.terms[start];
  else return SumTerm.buildNoClone(this.terms.slice(start,end));
}
Object.defineProperty(SumTerm.prototype,"constructor",{
  value:SumTerm,
  enumerable:false,
  writable:true
});

Term.ZERO=new Term("0");
Term.ONE=new Term("三_0(0)");
Term.SMALLOMEGA=new Term("三_0(1)");

/** @returns {boolean} */
function inT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return true; //1
  if (t instanceof SumTerm) return t.terms.every(inPT); //2
  if (t instanceof ThreeTerm) return inT(t.inner1)&&inT(t.inner2); //3
  return false;
}
function inPT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ThreeTerm) return inT(t.inner1)&&inT(t.inner2); //3
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
  if (S instanceof SumTerm){ //3
    if (T instanceof SumTerm) //3.1
      return lessThan(S.getLeft(),T.getLeft()) //3.1.1
        ||equal(S.getLeft(),T.getLeft())&&lessThan(S.getNotLeft(),T.getNotLeft()); //3.1.2
    if (T instanceof ThreeTerm) return lessThan(S.getLeft(),T); //3.2
  }
  if (S instanceof ThreeTerm){ //4
    if (T instanceof SumTerm) return lessThanOrEqual(S,T.getLeft()); //4.1
    if (T instanceof ThreeTerm) //4.2
      return lessThan(S.inner1,T.inner1) //4.2.1
        ||equal(S.inner1,T.inner1)&&lessThan(S.inner2,T.inner2); //4.2.2
  }
  throw Error("No rule to compute if "+S+"<"+T);
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns {string}
 */
function add(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (S instanceof ZeroTerm) return T+""; //1
  else if (T instanceof ZeroTerm) return S+""; //2
  else return S+"+"+T; //2
  throw Error("No rule to compute add("+S+","+T+")");
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns {boolean} ∃u.S=add(u,T)?
 */
function canCancelAddRight(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (T instanceof ZeroTerm) return true;
  if (T instanceof ThreeTerm){
    if (S instanceof ZeroTerm) return false;
    if (S instanceof ThreeTerm) return equal(S,T);
    if (S instanceof SumTerm) return equal(S.getRight(),T);
  }
  if (T instanceof SumTerm){
    if (S instanceof ZeroTerm) return false;
    if (S instanceof ThreeTerm) return false;
    if (S instanceof SumTerm) return equal(S.slice(-T.terms.length),T);
  }
  throw Error("No rule to compute if there exists u such that "+S+"=add(u,"+T+")");
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns {string} u.S=add(u,T)
 */
function cancelAddRight(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (!canCancelAddRight(S,T)) throw Error("No u exists such that "+S+"=add(u,"+T+")");
  if (T instanceof ZeroTerm) return S+"";
  if (T instanceof ThreeTerm){
    if (S instanceof ThreeTerm) return "0";
    if (S instanceof SumTerm) return S.getNotRight()+"";
  }
  if (T instanceof SumTerm){
    if (S instanceof SumTerm) return S.slice(0,-T.terms.length)+"";
  }
  throw Error("No rule to compute u such that "+S+"=add(u,"+T+")");
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns {boolean} ∃u.S=add(T,u)?
 */
function canCancelAddLeft(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (T instanceof ZeroTerm) return true;
  if (T instanceof ThreeTerm){
    if (S instanceof ZeroTerm) return false;
    if (S instanceof ThreeTerm) return equal(S,T);
    if (S instanceof SumTerm) return equal(S.getLeft(),T);
  }
  if (T instanceof SumTerm){
    if (S instanceof ZeroTerm) return false;
    if (S instanceof ThreeTerm) return false;
    if (S instanceof SumTerm) return equal(S.slice(0,T.terms.length),T);
  }
  throw Error("No rule to compute if there exists u such that "+S+"=add("+T+",u)");
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns {string} u.S=add(T,u)
 */
function cancelAddLeft(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (!canCancelAddLeft(S,T)) throw Error("No u exists such that "+S+"=add("+T+",u)");
  if (T instanceof ZeroTerm) return S+"";
  if (T instanceof ThreeTerm){
    if (S instanceof ThreeTerm) return "0";
    if (S instanceof SumTerm) return S.getNotLeft()+"";
  }
  if (T instanceof SumTerm){
    if (S instanceof SumTerm) return S.slice(T.terms.length)+"";
  }
  throw Error("No rule to compute u such that "+S+"=add("+T+",u)");
}
/**
 * @param {Term|string} S 
 * @returns {boolean} ∃t,a,b.S=add(t,三_a(b))?
 */
function canSeparateRight(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  return S instanceof ThreeTerm||S instanceof SumTerm;
  throw Error("No rule to compute if there exists t,a,b such that "+S+"=add(t,三_a(b))");
}
/**
 * @param {Term|string} S 
 * @returns {[Term,Term,Term]} t,a,b.S=add(t,三_a(b))
 */
function separateRight(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (!canSeparateRight(S)) throw Error("No t,a,b exists such that "+S+"=add(t,三_a(b))");
  if (S instanceof ThreeTerm) return [Term.ZERO,S.inner1,S.inner2];
  else if (S instanceof SumTerm){
    var S_getRight=S.getRight();
    if (!(S_getRight instanceof ThreeTerm)) throw Error("Unexpected error");
    return [S.getNotRight(),S_getRight.inner1,S_getRight.inner2];
  }
  throw Error("No rule to compute t,a,b such that "+S+"=add(t,三_a(b))");
}
/**
 * @param {Term|string} S 
 * @returns {string}
 */
function succ(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  return add(S,Term.ONE);
  throw Error("No rule to compute succ("+S+")");
}
/**
 * @param {Term|string} S 
 * @returns {boolean} ∃t.S=succ(t)?
 */
function isSucc(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof ZeroTerm) return false;
  if (S instanceof SumTerm) return equal(S.getRight(),Term.ONE);
  if (S instanceof ThreeTerm) return equal(S,Term.ONE);
  throw Error("No rule to compute if there exists t such that "+S+"=succ(t)");
}
/**
 * @param {Term|string} S 
 * @returns {string} t.S=succ(t)
 */
function pred(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (!isSucc(S)) throw Error("No t exists such that "+S+"=succ(t)");
  if (S instanceof SumTerm) return S.getNotRight()+"";
  if (S instanceof ThreeTerm) return "0";
  throw Error("No rule to compute t such that "+S+"=succ(t)");
}
/**
 * @param {Term|string} S
 * @returns {string}
 */
function dom(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm) return dom(S.getRight()); //2
  if (S instanceof ThreeTerm){ //3
    var a=S.inner1;
    var b=S.inner2;
    var dom_b=dom(b);
    var Term_dom_b=new Term(dom_b);
    if (equal(Term_dom_b,Term.ZERO)){ //3.1
      var dom_a=dom(a);
      var Term_dom_a=new Term(dom_a);
      if (equal(Term_dom_a,Term.ZERO)||equal(Term_dom_a,Term.ONE)) return S+""; //3.1.1
      else return dom_a; //3.1.2
    }else if (equal(Term_dom_b,Term.ONE)) return Term.SMALLOMEGA+""; //3.2
    else{ //3.3
      if (lessThan(Term_dom_b,S)) return dom_b; //3.3.1
      else if (!equal(Term_dom_b,"三("+succ(a)+",0)")) return Term.SMALLOMEGA+""; //3.3.2
      else return S+""; //3.3.3
    }
  }
  throw Error("No rule to compute dom("+S+")");
}
/**
 * @param {Term|string} S
 * @param {Term|string} T
 * @returns {string} sep_0(S,T)
 */
function sep0(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (inPT(S)&&lessThanOrEqual(T,S)) return S+"";
  if (S instanceof SumTerm){
    var i=0;
    while (i<S.terms.length&&lessThanOrEqual(T,S.terms[i])) i++;
    return S.terms.slice(0,i).reduce(add,"0"); //Note: Equivalent by associativity of add and 0 as identity of add
  }
  return "0";
  throw Error("No rule to compute sep_0("+S+","+T+")");
}
/**
 * @param {Term|string} S
 * @param {Term|string} T
 * @returns {string} sep_1(S,T)
 */
function sep1(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (inPT(S)&&lessThan(S,T)) return S+"";
  if (S instanceof SumTerm){
    var i=S.terms.length-1;
    while (i>=0&&lessThan(S.terms[i],T)) i--;
    return S.terms.slice(i+1).reduce(add,"0"); //Note: Equivalent by associativity of add and 0 as identity of add
  }
  return "0";
  throw Error("No rule to compute sep_1("+S+","+T+")");
}
/**
 * @param {Term|string} S
 * @param {Term|string} T
 * @param {Term|string} E
 * @param {Term|string} EP
 * @param {Term|string} F
 * @returns {string} subst_0(S,T,E,EP,F)
 */
function subst0(S,T,E,EP,F){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!(E instanceof Term)) E=new Term(E);
  if (!(EP instanceof Term)) EP=new Term(EP);
  if (!(F instanceof Term)) F=new Term(F);
  if (!inT(S)||!inT(T)||!inT(E)||!inT(EP)||!inT(F)) throw Error("Invalid argument: "+S+","+T+","+E+","+EP+","+F);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof ThreeTerm){
    var a=S.inner1;
    if (equal(S.inner2,Term.ZERO)){ //2
      if (equal(a,succ(E))) return "三("+E+","+T+")"; //2.1
      else return "三("+subst0(a,T,E,EP,F)+",0)"; //2.2
    }else if (canSeparateRight(S.inner2)){ //3
      var separateRight_S_inner2=separateRight(S.inner2);
      var b=separateRight_S_inner2[0];
      var c=separateRight_S_inner2[1];
      var d=separateRight_S_inner2[2];
      if (equal(c,succ(E))&&equal(d,Term.ZERO)){ //3.1
        var separateRight_T;
        if (canSeparateRight(T)&&equal((separateRight_T=separateRight(T))[1],EP)&&canCancelAddLeft(separateRight_T[2],F)){ //3.1.1
          var tp=separateRight_T[0];
          var dp=cancelAddLeft(separateRight_T[2],F);
          return add(subst0(S,tp,E,EP,F),"三("+a+","+add(b,dp)+")");
        }else return "0"; //3.1.2
      }else return "三("+a+","+subst0(add(b,"三("+c+","+d+")"),T,E,EP,F)+")"; //3.2
    }
  }
  if (S instanceof SumTerm) return add(S.getNotRight(),subst0(S.getRight(),T,E,EP,F)); //4
  throw Error("No rule to compute subst_0("+S+","+T+","+E+","+EP+","+F+")");
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @param {Term|string} C 
 * @returns {string} subst_1(S,T,C)
 */
function subst1(S,T,C){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!(C instanceof Term)) C=new Term(C);
  if (!inT(S)||!inT(T)||!inT(C)) throw Error("Invalid argument: "+S+","+T+","+C);
  if (canSeparateRight(S)&&canSeparateRight(T)){
    var separateRight_S=separateRight(S);
    var separateRight_T=separateRight(T);
    if (equal(separateRight_S[0],separateRight_T[0])){
      if (canSeparateRight(separateRight_S[1])&&equal(separateRight_S[2],Term.ZERO)&&canSeparateRight(separateRight_T[1])&&equal(separateRight_T[2],Term.ZERO)){ //1
        var separateRight_separateRight_S_1=separateRight(separateRight_S[1]);
        var separateRight_separateRight_T_1=separateRight(separateRight_T[1]);
        if (equal(separateRight_separateRight_S_1[0],separateRight_separateRight_T_1[0])){ //1
          var sp=separateRight_S[0];
          var a=separateRight_separateRight_S_1[0];
          var e=separateRight_separateRight_S_1[1];
          var f=separateRight_separateRight_S_1[2];
          var ep=separateRight_separateRight_T_1[1];
          var fp=separateRight_separateRight_T_1[2];
          if (equal(e,C)) return add(sp,"三("+add(a,"三("+C+","+fund(f,"三("+C+","+T+")")+")")+",0)"); //1.1
          else return add(sp,"三("+subst1(add(a,"三("+e+","+f+")"),add(a,"三("+ep+","+fp+")"),C)+",0)"); //1.2
        }
      }
      if (equal(separateRight_S[1],separateRight_T[1])&&canSeparateRight(separateRight_S[2])&&canSeparateRight(separateRight_T[2])){ //1
        var separateRight_separateRight_S_2=separateRight(separateRight_S[2]);
        var separateRight_separateRight_T_2=separateRight(separateRight_T[2]);
        if (equal(separateRight_separateRight_S_2[0],separateRight_separateRight_T_2[0])){ //2
          var sp=separateRight_S[0];
          var a=separateRight_S[1];
          var b=separateRight_separateRight_S_2[0];
          var e=separateRight_separateRight_S_2[1];
          var f=separateRight_separateRight_S_2[2];
          var ep=separateRight_separateRight_T_2[1];
          var fp=separateRight_separateRight_T_2[2];
          if (equal(e,C)) return subst0(S,T,C,a,sep0(b,"三("+succ(C)+",0)")); //2.1
          else return add(sp,"三("+a+","+subst1(add(b,"三("+e+","+f+")"),add(b,"三("+ep+","+fp+")"),C)+")"); //2.2
        }
      }
    }
  }
  return "0"; //3
  throw Error("No rule to compute subst_1("+S+","+T+","+C+")");
}
/**
 * @param {Term|string} S 
 * @param {Term|number|string} T 
 * @returns {string} S[T]
 */
function fund(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (typeof T=="number") T=String(T);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm){ //2
    var a=S.getLeft();
    var b=S.getNotLeft();
    var fund_b_n=fund(b,T);
    if (equal(fund_b_n,Term.ZERO)) return a+""; //2.1
    else return a+"+"+fund_b_n; //2.2
  }
  if (S instanceof ThreeTerm){ //3
    var a=S.inner1;
    var b=S.inner2;
    var dom_b=dom(b);
    var Term_dom_b=new Term(dom_b);
    if (equal(Term_dom_b,Term.ZERO)){ //3.1
      var dom_a=dom(a);
      var Term_dom_a=new Term(dom_a);
      if (equal(Term_dom_a,Term.ZERO)||equal(Term_dom_a,Term.ONE)) return T+""; //3.1.1
      else return "三("+fund(a,T)+",0)"; //3.1.2
    }else if (equal(Term_dom_b,Term.ONE)){ //3.2
      var Term_fund_T_0=null;
      if (equal(T,(Term_fund_T_0=new Term(fund(T,Term.ZERO)))+"+"+Term.ONE)) return fund(S,Term_fund_T_0)+"+"+fund(S,Term.ONE); //3.2.1
      else return "三("+a+","+fund(b,Term.ZERO)+")"; //3.2.2
    }else{ //3.3
      var c=null;
      var d=null;
      if (lessThan(Term_dom_b,S)) return "三("+a+","+fund(b,T)+")"; //3.3.1
      else if (Term_dom_b instanceof ThreeTerm&&isSucc(Term_dom_b.inner1)&&equal(Term_dom_b.inner2,Term.ZERO)&&lessThan(a,c=pred(Term_dom_b.inner1))){ //3.3.2
        var Term_fund_T_0=null;
        var Term_fund_S_fund_T_0=null;
        if (equal(T,succ(Term_fund_T_0=new Term(fund(T,Term.ZERO))))&&(Term_fund_S_fund_T_0=new Term(fund(S,Term_fund_T_0))) instanceof ThreeTerm&&equal(Term_fund_S_fund_T_0.inner1,a)) return "三("+a+","+fund(b,"三("+c+","+Term_fund_S_fund_T_0.inner2+")")+")"; //3.3.2.1
        else return "三("+a+","+fund(b,"三("+c+",0)")+")"; //3.3.2.2
      }else if (Term_dom_b instanceof ThreeTerm&&equal(dom(d=Term_dom_b.inner2),"三("+succ(c=Term_dom_b.inner1)+",0)")){ //3.3.3
        var Term_fund_T_0=null;
        var Term_fund_S_fund_T_0=null;
        var Term_tail_bc=null;
        if (equal(T,succ(Term_fund_T_0=new Term(fund(T,Term.ZERO))))&&(Term_fund_S_fund_T_0=new Term(fund(S,Term_fund_T_0))) instanceof ThreeTerm&&equal(Term_fund_S_fund_T_0.inner1,a)){ //3.3.3.1
          var bp=Term_fund_S_fund_T_0.inner2;
          var Term_tsucc_c0=new Term("三("+succ(c)+",0)");
          var sep1_bp_Term_tsucc_c0=sep1(bp,Term_tsucc_c0);
          var Term_sep1_bp_Term_tsucc_c0=new Term(sep1_bp_Term_tsucc_c0);
          if (equal(Term_sep1_bp_Term_tsucc_c0,Term.ZERO)) return "三("+a+","+subst1(b,bp,c)+")"; //3.3.3.1.1
          else return "三("+a+","+fund(b,"三("+c+","+fund(d,Term_sep1_bp_Term_tsucc_c0)+")")+")"; //3.3.3.1.2
        }else return "三("+a+","+fund(b,"三("+c+","+fund(d,Term.ZERO)+")")+")"; //3.3.3.2
      }else return T+""; //3.3.4
    }
  }
  throw Error("No rule to compute "+S+"["+T+"]");
}
/**
 * @param {number} n 
 * @returns ┌n┐ 
 */
function fromNumber(n){
  if (n==0) return "0"; //1
  else if (n==1) return Term.ONE+""; //2
  else return (Term.ONE+"+").repeat(n-1)+"+"+Term.ONE; //3
}
/**
 * @param {Term|string} S 
 * @param {number} m 
 * @param {number} n 
 * @returns {number}
 */
function FGH(S,m,n){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)||typeof m!="number"||typeof n!="number") throw Error("Invalid argument: "+S+","+m+","+n);
  if (m==0) return n; //1
  else if (m==1){ //2
    var dom_S=dom(S);
    var Term_dom_S=new Term(dom_S);
    if (equal(Term_dom_S,Term.ZERO)) return n+1; //2.1
    else if (equal(Term_dom_S,Term.ONE)) return FGH(fund(S,Term.ZERO),n,n); //2.2
    else return FGH(fund(S,fromNumber(n)),1,n); //2.3
  }else return FGH(S,1,FGH(S,m-1,n)); //3
}
/**
 * @param {number} n 
 * @returns {string} 三(0,三(0,Λ(n)))
 */
function limitOrd(n){
  return "三(0,三(0,"+(n==0?"0":"三(".repeat(n)+"0"+",0)".repeat(n))+"))";
}
/**
 * @param {number} n 
 * @returns {number} lim_三(n)
 */
function limitFunction(n){
  if (typeof n!="number") throw Error("Invalid argument");
  return FGH(limitOrd(n),1,n);
}
/**
 * @param {number} n 
 * @returns {number} Lim_三(n)
 */
function largeFunction(n){
  if (typeof n!="number") throw Error("Invalid argument");
  var r=n;
  for (var i=0;i<n;i++) r=limitFunction(r);
  return r;
}
function findOTPath(x,limit){
  if (!(x instanceof Term)) x=new Term(x);
  if (!inT(x)) throw Error("Invalid argument: "+x);
  if (typeof limit=="undefined"||limit==-1) limit=Infinity;
  if (equal(x,Term.ZERO)){
    return {isStandard:true,path:["0"],funds:[-1]};
  }else{
    var n=0;
    var t;
    while(n<=limit&&!(equal(x,t=limitOrd(n))||lessThan(x,t))){
      n++;
    };
    if (n>limit) return {isStandard:false,path:[],funds:[]};
    t=limitOrd(n);
    console.log(t);
    var r={isStandard:false,path:[t],funds:[n]};
    while (!equal(x,t)){
      n=0;
      var nt;
      while (n<=limit&&lessThan(nt=fund(t,n),x)) n++;
      if (n>limit) return r;
      r.path.push(t=nt);
      r.funds.push(n);
      console.log(nt);
    }
    r.isStandard=true;
    return r;
  }
}
function isStandard(x,limit){
  return findOTPath(x,limit).isStandard;
}

/** @type {[string,number][]} */
var testTermsPre=[
  ["0",-1],
  ["1",-1],
  ["ω",3],
  ["三_0(2)",3],
  ["三_0(ω)",3],
  ["三_0(三_0(ω))",3],
  ["三_0(三_0(三_1(0)))",3],
  ["三_0(三_0(三_1(0))+1)",3],
  ["三_0(三_0(三_1(0))+三_0(三_0(三_1(0))))",3],
  ["三_0(三_0(三_1(0))+三_0(三_1(0)))",3],
  ["三_0(三_0(三_1(0)+1))",3],
  ["三_0(三_0(三_1(0)+三_0(三_0(三_1(0)))))",3],
  ["三_0(三_0(三_1(0)+三_0(三_1(0))))",3],
  ["三_0(三_0(三_1(0)+三_0(三_1(0)+三_0(三_1(0)))))",3],
  ["三_0(三_0(三_1(0)+三_1(0)))",3],
  ["三_0(三_0(三_1(0)+三_1(0))+三_0(三_0(三_1(0)+三_1(0))))",3],
  ["三_0(三_0(三_1(0)+三_1(0))+三_0(三_1(0)))",3],
  ["三_0(三_0(三_1(0)+三_1(0))+三_0(三_1(0)+三_0(三_1(0)+三_1(0))))",3],
  ["三_0(三_0(三_1(0)+三_1(0))+三_0(三_1(0)+三_1(0)))",3],
  ["三_0(三_0(三_1(0)+三_1(0)+1))",-1],
  ["三_0(三_0(三_1(0)+三_1(0)+三_0(三_1(0))))",3],
  ["三_0(三_0(三_1(0)+三_1(0)+三_0(三_1(0)+三_1(0))))",3],
  ["三_0(三_0(三_1(0)+三_1(0)+三_1(0)))",3],
  ["三_0(三_0(三_1(0)+三_1(0)+三_1(0))+三_0(三_1(0)+三_0(三_1(0)+三_1(0)+三_1(0))))",3],
  ["三_0(三_0(三_1(0)+三_1(0)+三_1(0)+三_1(0)))",-1],
  ["三_0(三_0(三_1(1)))",3],
  ["三_0(三_0(三_1(ω)))",3],
  ["三_0(三_0(三_1(三_0(三_0(三_1(0))))))",3],
  ["三_0(三_0(三_1(三_0(三_1(0)))))",3],
  ["三_0(三_0(三_1(三_1(0))))",3],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(0)))",3],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(0)+三_0(三_1(三_1(0)))))",3],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(0)+三_1(0)))",-1],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(三_0(三_0(三_1(三_1(0)))))))",-1],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(三_0(三_1(0)))))",-1],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(三_0(三_1(三_1(0))))))",3],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(三_0(三_1(三_1(0))))+三_0(三_1(三_1(0)))))",3],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(三_0(三_1(三_1(0))))+三_1(0)))",3],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(三_0(三_1(三_1(0))))+三_1(三_0(三_1(三_1(0))))))",3],
  ["三_0(三_0(三_1(三_1(0)))+三_0(三_1(三_1(0))))",3],
  ["三_0(三_0(三_1(三_1(0))+1))",3],
  ["三_0(三_0(三_1(三_1(0))+三_0(三_1(0))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_0(三_1(三_0(三_1(三_1(0)))))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_0(三_1(三_0(三_1(三_1(0))))+三_0(三_1(三_1(0))))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_0(三_1(三_1(0)))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_0(三_1(三_1(0))))+三_0(三_1(三_0(三_1(三_1(0))+三_0(三_1(三_1(0)))))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_0(三_1(三_1(0))+三_0(三_1(三_1(0))))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_1(0)))",3],
  ["三_0(三_0(三_1(三_1(0))+三_1(0))+三_0(三_1(三_0(三_1(三_1(0))+三_1(0)))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_1(0)+三_1(0)))",-1],
  ["三_0(三_0(三_1(三_1(0))+三_1(三_1(0))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_1(三_1(0)))+三_0(三_1(三_0(三_1(三_1(0))+三_0(三_1(三_1(0)))))))",3],
  ["三_0(三_0(三_1(三_1(0))+三_1(三_1(0)))+三_0(三_1(三_0(三_1(三_1(0))+三_1(三_1(0))))))",3],
  ["三_0(三_0(三_1(三_1(0)+1)))",3],
  ["三_0(三_0(三_1(三_1(0)+三_0(三_0(三_1(三_1(0)))))))",-1],
  ["三_0(三_0(三_1(三_1(0)+三_0(三_1(0)))))",3],
  ["三_0(三_0(三_1(三_1(0)+三_1(0))))",3],
  ["三_0(三_0(三_1(三_1(1))))",3],
  ["三_0(三_0(三_1(三_1(三_0(三_1(0))))))",3],
  ["三_0(三_0(三_1(三_1(三_0(三_1(三_0(三_1(三_1(0)))))))))",3],
  ["三_0(三_0(三_1(三_1(三_0(三_1(三_1(0)))))))",3],
  ["三_0(三_0(三_1(三_1(三_1(0)))))",3],
  ["三_0(三_0(三_1(三_1(三_1(0))))+三_0(三_1(三_0(三_1(三_1(三_1(0)))))))",3],
  ["三_0(三_0(三_1(三_1(三_1(0))))+三_0(三_1(三_1(三_0(三_1(三_1(三_1(0))))))))",3],
  ["三_0(三_0(三_1(三_1(三_1(三_1(0))))))",-1],
  ["三_0(三_0(三_2(0)))",3],
  ["三_0(三_0(三_2(0))+三_0(三_0(三_2(0))))",3],
  ["三_0(三_0(三_2(0))+三_0(三_1(0)))",3],
  ["三_0(三_0(三_2(0))+三_0(三_2(0)))",3],
  ["三_0(三_0(三_2(0)+三_0(三_2(0))))",3],
  ["三_0(三_0(三_2(0)+三_1(0)))",3],
  ["三_0(三_0(三_2(0)+三_1(0)+三_0(三_2(0)+三_0(三_2(0)+三_1(0)))))",3],
  ["三_0(三_0(三_2(0)+三_1(0)+三_0(三_2(0)+三_1(0))))",3],
  ["三_0(三_0(三_2(0)+三_1(三_2(0))))",3],
  ["三_0(三_0(三_2(0)+三_1(三_2(0)+三_1(三_1(三_2(0))))))",3],
  ["三_0(三_0(三_2(0)+三_1(三_2(0)+三_1(三_2(0)))))",3],
  ["三_0(三_0(三_2(0)+三_2(0)))",3],
  ["三_0(三_0(三_2(0)+三_2(0)+三_1(三_2(0)+三_2(0))))",-1],
  ["三_0(三_0(三_2(0)+三_2(0)+三_1(三_2(0)+三_2(0)+三_1(三_1(三_2(0)+三_2(0))))))",3],
  ["三_0(三_0(三_2(0)+三_2(0)+三_1(三_2(0)+三_2(0)+三_1(三_2(0)))))",-1],
  ["三_0(三_0(三_2(0)+三_2(0)+三_1(三_2(0)+三_2(0)+三_1(三_2(0)+三_1(三_2(0))))))",3],
  ["三_0(三_0(三_2(0)+三_2(0)+三_1(三_2(0)+三_2(0)+三_1(三_2(0)+三_1(三_2(0)+三_2(0))))))",3],
  ["三_0(三_0(三_2(1)))",-1],
  ["三_0(三_0(三_2(三_0(三_0(三_2(0))))))",-1],
  ["三_0(三_0(三_2(三_0(三_1(0)))))",-1],
  ["三_0(三_0(三_2(三_0(三_2(0)))))",-1],
  ["三_0(三_0(三_2(三_1(0))))",3],
  ["三_0(三_0(三_2(三_1(0)))+三_0(三_2(三_0(三_2(三_1(0))))))",3],
  ["三_0(三_0(三_2(三_1(0)))+三_0(三_2(三_1(0))))",3],
  ["三_0(三_0(三_2(三_1(0))+三_1(0)))",-1],
  ["三_0(三_0(三_2(三_1(0)+三_1(0))))",-1],
  ["三_0(三_0(三_2(三_1(三_2(0)))))",3],
  ["三_0(三_0(三_2(三_2(0))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_0(三_1(三_0(三_2(三_1(0)))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_0(三_1(三_0(三_2(三_1(三_2(0))))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_0(三_1(三_0(三_2(三_2(0)))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_0(三_2(三_0(三_2(三_1(0)))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_0(三_2(三_0(三_2(三_1(三_2(0))))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_0(三_2(三_0(三_2(三_2(0)))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_0(三_2(三_2(0)))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_1(0)))",-1],
  ["三_0(三_0(三_2(三_2(0))+三_1(三_2(三_2(0)))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_1(三_2(三_2(0))+三_1(三_2(三_1(三_2(三_2(0))))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_1(三_2(三_2(0))+三_1(三_2(三_1(三_2(三_2(0))))+三_2(三_1(三_2(三_2(0))))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_1(三_2(三_2(0))+三_1(三_2(三_1(三_2(三_2(0)))+三_1(三_2(三_2(0))))))))",3],
  ["三_0(三_0(三_2(三_2(0))+三_2(0)))",3],
  ["三_0(三_0(三_3(0)))",3],
  ["三_0(三_0(三_ω(0)))",3],
  ["三_0(三_0(三_ω(三_0(三_ω(0)))))",-1],
  ["三_0(三_0(三_ω(三_1(0))))",-1],
  ["三_0(三_0(三_ω(三_1(三_ω(0)))))",-1],
  ["三_0(三_0(三_ω(三_ω(0))))",-1],
  ["三_0(三_0(三_{ω+1}(0)))",3],
  ["三_0(三_0(三_{ω+1}(0)+三_ω(三_{ω+1}(0))))",3],
  ["三_0(三_0(三_{ω+1}(0)+三_{ω+1}(0)))",3],
  ["三_0(三_0(三_{ω+1}(三_1(0))))",-1],
  ["三_0(三_0(三_{ω+1}(三_1(三_{ω+1}(0)))))",3],
  ["三_0(三_0(三_{ω+1}(三_ω(三_{ω+1}(0)))))",3],
  ["三_0(三_0(三_{ω+1}(三_{ω+1}(0))))",3],
  ["三_0(三_0(三_三_0(三_0(三_1(0)))(0)))",3],
  ["三_0(三_0(三_三_0(三_0(三_1(三_1(0))))(0)))",3],
  ["三_0(三_0(三_三_0(三_1(0))(0)))",3],
  ["三_0(三_0(三_三_0(三_1(0))(0))+三_0(三_0(三_三_0(三_1(0))(0))))",3],
  ["三_0(三_0(三_三_0(三_1(0))(0))+三_0(三_1(0)+三_0(三_三_0(三_1(0))(0))))",3],
  ["三_0(三_0(三_三_0(三_1(0))(0))+三_0(三_三_0(三_1(0))(0)))",3],
  ["三_0(三_0(三_三_0(三_1(0))(0)+三_0(三_0(三_三_0(三_1(0))(0)))))",3],
  ["三_0(三_0(三_三_0(三_1(0))(0)+三_0(三_三_0(三_1(0))(0))))",3],
  ["三_0(三_0(三_三_0(三_1(0))(0)+三_1(0)))",-1],
  ["三_0(三_0(三_三_0(三_1(0))(1)))",-1],
  ["三_0(三_0(三_三_0(三_1(0)+三_1(0))(0)))",3],
  ["三_0(三_0(三_三_0(三_1(0)+三_1(0))(0))+三_0(三_0(三_三_0(三_1(0)+三_1(0))(0))))",3],
  ["三_0(三_0(三_三_0(三_1(0)+三_1(0))(0))+三_0(三_1(0)+三_0(三_三_0(三_1(0)+三_1(0))(0))))",3],
  ["三_0(三_0(三_三_0(三_1(0)+三_1(0))(0)+三_0(三_0(三_三_0(三_1(0)+三_1(0))(0)))))",-1],
  ["三_0(三_0(三_三_0(三_1(0)+三_1(0))(0)+三_0(三_1(0)+三_0(三_三_0(三_1(0)+三_1(0))(0)))))",-1],
  ["三_0(三_0(三_三_0(三_1(0)+三_1(0)+三_1(0))(0)))",-1],
  ["三_0(三_0(三_三_0(三_1(1))(0)))",-1],
  ["三_0(三_0(三_三_0(三_1(三_1(0)))(0)))",3],
  ["三_0(三_0(三_三_0(三_2(0))(0)))",3],
  ["三_0(三_0(三_三_0(三_2(0)+三_1(0))(0)))",3],
  ["三_0(三_0(三_三_0(三_ω(0))(0)))",-1],
  ["三_0(三_0(三_三_1(0)(0)))",3],
  ["三_0(三_0(三_三_1(0)(0))+三_0(三_0(三_三_1(0)(0))))",3],
  ["三_0(三_0(三_三_1(0)(0))+三_0(三_1(0)+三_0(三_三_1(0)(0))))",3],
  ["三_0(三_0(三_三_1(0)(0))+三_0(三_三_1(0)(0)))",3],
  ["三_0(三_0(三_三_1(三_0(三_1(0)))(0)))",-1],
  ["三_0(三_0(三_三_1(三_1(0))(0)))",-1],
  ["三_0(三_0(三_三_1(三_2(0))(0)))",3],
  ["三_0(三_0(三_三_1(三_2(0))(0)+三_0(三_三_1(三_2(0))(0))))",3],
  ["三_0(三_0(三_三_1(三_2(0))(0)+三_1(三_三_1(三_2(0))(0))))",3],
  ["三_0(三_0(三_三_1(三_2(三_2(0)))(0)))",3],
  ["三_0(三_0(三_三_2(0)(0)))",3],
  ["三_0(三_0(三_三_2(0)(0))+三_0(三_三_2(0)(0)))",-1],
  ["三_0(三_0(三_三_2(0)(0)+三_0(三_三_2(0)(0))))",3],
  ["三_0(三_0(三_三_2(0)(0)+三_1(三_三_2(0)(0))))",3],
  ["三_0(三_0(三_三_2(0)(0)+三_2(三_三_2(0)(0))))",3],
  ["三_0(三_0(三_三_2(0)(0)+三_三_0(三_2(0))(0)))",-1],
  ["三_0(三_0(三_三_2(0)(0)+三_三_0(三_三_2(0)(0))(0)))",3],
  ["三_0(三_0(三_三_2(0)(0)+三_三_1(三_1(三_2(0)))(0)))",3],
  ["三_0(三_0(三_三_2(0)(0)+三_三_1(三_2(0))(0)))",3],
  ["三_0(三_0(三_三_2(0)(0)+三_三_1(三_三_1(三_三_2(0)(0))(0))(0)))",3],
  ["三_0(三_0(三_三_2(0)(0)+三_三_1(三_三_2(0)(0))(0)))",3],
  ["三_0(三_0(三_三_2(0)(三_1(三_三_2(0)(0)))))",3],
  ["三_0(三_0(三_三_2(三_1(三_三_2(0)(0)))(0)))",3],
  ["三_0(三_0(三_三_3(0)(0)))",-1],
  ["三_0(三_0(三_三_ω(0)(0)))",-1],
  ["三_0(三_0(三_三_三_1(0)(0)(0)))",3]
];
/** @type {string[]}} */
var testTerms;
function setupTestTerms(){
  document.getElementById('input').value=testTermsPre.filter(function (t){return t[1]>=0;}).map(function(t){return "fund "+t[0]+" "+t[1];}).join("\n");
  testTerms=testTermsPre.map(function (t){return t[0];});
}
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
      result=isStandard(testTerms[i],10);
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
  "2三",
  "1三"
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
      console.time(line);
      try{
        if (cmd=="normalize"||cmd=="norm"){
          result=normalizeAbbreviations(args[0]);
        }else if (cmd=="abbreviate"||cmd=="abbr"){
          result=null;
        }else if (cmd=="inT"){
          result=inT(args[0]);
        }else if (cmd=="inPT"){
          result=inPT(args[0]);
        }else if (cmd=="lessThanOrEqual"||cmd=="<="){
          result=lessThanOrEqual(args[0],args[1]);
        }else if (cmd=="lessThan"||cmd=="<"){
          result=lessThan(args[0],args[1]);
        }else if (cmd=="add"){
          result=add(args[0],args[1]);
        }else if (cmd=="canCancelAddRight"){
          result=canCancelAddRight(args[0],args[1]);
        }else if (cmd=="cancelAddRight"){
          result=cancelAddRight(args[0],args[1]);
        }else if (cmd=="canCancelAddLeft"){
          result=canCancelAddLeft(args[0],args[1]);
        }else if (cmd=="cancelAddLeft"){
          result=cancelAddLeft(args[0],args[1]);
        }else if (cmd=="canSeparateRight"){
          result=canSeparateRight(args[0]);
        }else if (cmd=="separateRight"){
          result=separateRight(args[0]);
        }else if (cmd=="succ"){
          result=succ(args[0]);
        }else if (cmd=="isSucc"){
          result=isSucc(args[0]);
        }else if (cmd=="pred"){
          result=pred(args[0]);
        }else if (cmd=="dom"){
          result=dom(args[0]);
        }else if (cmd=="sep0"){
          result=sep0(args[0],args[1]);
        }else if (cmd=="sep1"){
          result=sep1(args[0],args[1]);
        }else if (cmd=="subst0"){
          result=subst0(args[0],args[1],args[2],args[3],args[4]);
        }else if (cmd=="subst1"){
          result=subst1(args[0],args[1],args[2]);
        }else if (cmd=="fund"||cmd=="expand"){
          var t=normalizeAbbreviations(args[0]);
          result=[t];
          for (var i=1;i<args.length;i++){
            result.push(t=fund(t,args[i]));
          }
        }else if (cmd=="inOT"||cmd=="isStandard"){
          result=findOTPath(args[0],args[1]||3);
        }else{
          result=null;
        }
      }catch(e){
        result=e;
        console.error(e);
      }
      last[l]=result;
      console.timeEnd(line);
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
    }else if (cmd=="lessThanOrEqual"||cmd=="<="){
      output+=result;
    }else if (cmd=="lessThan"||cmd=="<"){
      output+=result;
    }else if (cmd=="add"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="canCancelAddRight"){
      output+=result;
    }else if (cmd=="cancelAddRight"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="canCancelAddLeft"){
      output+=result;
    }else if (cmd=="cancelAddLeft"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="canSeparateRight"){
      output+=result;
    }else if (cmd=="separateRight"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="succ"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="isSucc"){
      output+=result;
    }else if (cmd=="pred"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="dom"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="sep0"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="sep1"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="subst0"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="subst1"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="fund"||cmd=="expand"){
      if (options.detail){
        for (var i=1;i<result.length;i++){
          output+=abbreviateIfEnabled(result[i-1])+"["+args[i]+"]="+abbreviateIfEnabled(result[i])+(i==result.length-1?"":"\n");
        }
      }else{
        output+=abbreviateIfEnabled(result[result.length-1]);
      }
    }else if (cmd=="inOT"||cmd=="isStandard"){
      if (options.detail){
        for (var i=1;i<result.path.length;i++){
          output+=abbreviateIfEnabled(result.path[i-1])+"["+result.funds[i]+"]="+abbreviateIfEnabled(result.path[i])+"\n";
        }
        if (result.isStandard) output+=abbreviateIfEnabled(args[0])+"∈OT";
        else output+=abbreviateIfEnabled(args[0])+"∉OT limited to n≦"+(args[1]||3);
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