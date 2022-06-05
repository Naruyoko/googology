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
    else if (state==PLUS){
      if (r instanceof Array) r.push(SumTerm.buildNoClone([r.pop(),term]));
      else r=SumTerm.buildNoClone([r,term]);
    }else if (state==COMMA){
      if (r instanceof Array) r.push(term);
      else r=[r,term];
    }else throw Error("Wrong state when attempting to append as sum");
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
  /** @type {Term|Term[]} */
  var r=null;
  var startpos=scanner.pos;
  var TOP=0;
  var FOURTERMSUBSCRIPT=1;
  var FOURTERMINNER=2;
  var ARRAYINNER=3;
  var BRACES=4;
  var contextNames=["TOP","FOURTERMSUBSCRIPT","FOURTERMINNER","ARRAYINNER","BRACES"];
  if (typeof context=="undefined") context=TOP;
  var START=0;
  var PLUS=1;
  var COMMA=2;
  var CLOSEDTERM=3;
  var EXIT=4;
  var stateNames=["START","PLUS","COMMA","CLOSEDTERM","EXIT"];
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
      if (state!=START&&state!=PLUS&&state!=COMMA) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
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
      if (state!=START&&state!=PLUS&&state!=COMMA) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(Term.SMALLOMEGA.clone());
    }else if (nextWord=="Ω"||nextWord=="W"){
      if (state!=START&&state!=PLUS&&state!=COMMA) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(Term.LARGEOMEGA.clone());
    }else if (nextWord=="M"){
      if (state!=START&&state!=PLUS&&state!=COMMA) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(Term.M.clone());
    }else if (nextWord=="+"){
      if (state==CLOSEDTERM){
        state=PLUS;
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (nextWord==","){
      if (state==CLOSEDTERM){
        state=COMMA;
      }else throw Error("Unexpected character , at position "+scanpos+" in expression "+scanner.s);
    }else if (nextWord=="四"||nextWord=="f"||nextWord=="four"){
      if (state!=START&&state!=PLUS&&state!=COMMA) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var nextnext=scanner.next();
      if (nextnext=="_"){
        var subscriptterm=Term.build(scanner,FOURTERMSUBSCRIPT);
        var nextnext=scanner.next();
        if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        var innerterm=Term.build(scanner,FOURTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        if (innerterm instanceof ArrayTerm) appendToRSum(FourTerm.buildNoClone(ArrayTerm.buildNoClone([subscriptterm].concat(innerterm.rest),innerterm.one,innerterm.zero)));
        else appendToRSum(FourTerm.buildNoClone(ArrayTerm.buildNoClone(subscriptterm,innerterm)));
      }else if (nextnext=="("){
        var innerterm=Term.build(scanner,FOURTERMINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(FourTerm.buildNoClone(innerterm));
      }else throw Error("Expected _ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
    }else if (nextWord=="("){
      if (state!=START&&state!=PLUS&&state!=COMMA) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (scanner.peek()==")"){
        scanner.move(1);
        appendToRSum(ZeroTerm.build());
      }else{
        var innerterm=Term.build(scanner,ARRAYINNER);
        var nextnext=scanner.next();
        if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        appendToRSum(innerterm);
      }
    }else if (nextWord=="{"){
      if (state!=START&&state!=PLUS&&state!=COMMA) throw Error("Unexpected character { at position "+scanpos+" in expression "+scanner.s);
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
      }else if (context==FOURTERMSUBSCRIPT&&peek=="("){
        state=EXIT;
      }else if (context==FOURTERMINNER&&peek==")"){
        state=EXIT;
      }else if (context==ARRAYINNER&&peek==")"){
        state=EXIT;
      }
    }
  }
  if (context==TOP){
    if (scanner.hasNext()) throw Error("Something went wrong");
    if (state==START) r=ZeroTerm.build();
    else if (state==PLUS) throw Error("Unexpected end of input");
    else if (state==COMMA) throw Error("Unexpected end of input");
    else if (state==CLOSEDTERM){}
  }else{
    if (state==START) r=ZeroTerm.build();
    else if (state==PLUS) throw Error("Something went wrong");
    else if (state==COMMA) throw Error("Something went wrong");
    else if (state==CLOSEDTERM){}
  }
  if (r instanceof Array||context==ARRAYINNER) r=ArrayTerm.buildNoClone(r);
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
  return abbreviate&&(abbreviate===true||abbreviate["0"])?"0":"()";
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
 * @returns {FourTerm}
 */
function FourTerm(s){
  if (s instanceof FourTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof FourTerm)) return new FourTerm(s);
  /** @type {FourTerm} */
  Term.call(this,s);
  if (s&&!(this instanceof FourTerm)) throw Error("Invalid expression: "+s);
  /** @type {Term&ArrayTerm} */
  this.inner=null;
}
Object.assign(FourTerm,Term);
FourTerm.build=function (inner){
  var r=new FourTerm();
  if (inner instanceof ArrayTerm) r.inner=inner.clone();
  else r.inner=ArrayTerm.build(inner);
  return r;
}
/**
 * @param {Term} inner 
 * @returns {FourTerm}
 */
FourTerm.buildNoClone=function (inner){
  var r=new FourTerm();
  if (inner instanceof ArrayTerm) r.inner=inner;
  else r.inner=ArrayTerm.buildNoClone(inner);
  return r;
}
FourTerm.prototype=Object.create(Term.prototype);
FourTerm.prototype.clone=function (){
  return FourTerm.build(this.inner);
}
/** @param {boolean} abbreviate */
FourTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    if ((abbreviate===true||abbreviate["1"])&&this.equal(Term.ONE)) return "1";
    else if ((abbreviate===true||abbreviate["ω"])&&this.equal(Term.SMALLOMEGA)) return "ω";
    else if ((abbreviate===true||abbreviate["Ω"])&&this.equal(Term.LARGEOMEGA)) return "Ω";
    else if ((abbreviate===true||abbreviate["M"])&&this.equal(Term.M)) return "M";
    else if ((abbreviate===true||abbreviate["1四"])&&this.inner.rest.length==0&&this.inner.one.equal(Term.ZERO)) return "四("+this.inner.zero.toString(abbreviate)+")";
    else if ((abbreviate===true||abbreviate["2四"])&&this.inner.rest.length==0) return "四_"+this.inner.one.toStringWithImplicitBrace(abbreviate)+"("+this.inner.zero.toString(abbreviate)+")";
  }
  return "四("+this.inner.toString(abbreviate)+")";
}
FourTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof FourTerm&&this.inner.equal(other.inner);
}
Object.defineProperty(FourTerm.prototype,"constructor",{
  value:FourTerm,
  enumerable:false,
  writable:true
});

/**
 * @extends {Term}
 * @constructor
 * @param {*} s 
 * @returns {ArrayTerm}
 */
function ArrayTerm(s){
  if (s instanceof ArrayTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof ArrayTerm)) return new ArrayTerm(s);
  Term.call(this,s);
  if (s&&!(this instanceof ArrayTerm)) throw Error("Invalid expression: "+s);
  /** @type {(Term&ArrayTerm)[]} */
  this.rest=null;
  /** @type {Term} */
  this.one=null;
  /** @type {Term} */
  this.zero=null;
}
Object.assign(ArrayTerm,Term);
/**
 * @param {(Term|ArrayTerm)[]} rest 
 * @param {Term=} one 
 * @param {Term=} zero 
 * @returns {ArrayTerm}
 */
ArrayTerm.build=function (rest,one,zero){
  var r=new ArrayTerm();
  if (rest instanceof Array){
    if (typeof one=="undefined"){
      var o=rest[rest.length-1] instanceof ArrayTerm?rest[rest.length-2] instanceof ArrayTerm?0:1:2;
      r.rest=[];
      for (var i=0;i<rest.length-o;i++){
        if (rest[i] instanceof ArrayTerm) r.rest.push(new Term(rest[i]));
        else if (!rest[i].equal(Term.ZERO)) r.rest.push(ArrayTerm.buildNoClone(new Term(rest.length-i-1),new Term(rest[i])));
      }
      r.one=o>=2?new Term(rest[rest.length-2]):ZeroTerm.build();
      r.zero=o>=1?new Term(rest[rest.length-1]):ZeroTerm.build();
    }else{
      r.rest=[];
      for (var i=0;i<rest.length;i++){
        if (rest[i] instanceof ArrayTerm) r.rest.push(new Term(rest[i]));
        else if (!rest[i].equal(Term.ZERO)) r.rest.push(ArrayTerm.buildNoClone(new Term(rest.length-i+1),new Term(rest[i])));
      }
      r.one=new Term(one);
      r.zero=new Term(zero);
    }
  }else{
    if (typeof one=="undefined"){
      r.rest=[];
      r.one=Term.ZERO.clone();
      r.zero=new Term(rest);
    }else{
      r.rest=[];
      r.one=new Term(rest);
      r.zero=new Term(one);
    }
  }
  return r;
}
/**
 * @param {Term|Term[]} rest 
 * @param {Term=} one 
 * @param {Term=} zero 
 * @returns {ArrayTerm}
 */
ArrayTerm.buildNoClone=function (rest,one,zero){
  var r=new ArrayTerm();
  if (rest instanceof Array){
    if (typeof one=="undefined"){
      var o=rest[rest.length-1] instanceof ArrayTerm?rest[rest.length-2] instanceof ArrayTerm?0:1:2;
      r.rest=[];
      for (var i=0;i<rest.length-o;i++){
        if (rest[i] instanceof ArrayTerm) r.rest.push(rest[i]);
        else if (!rest[i].equal(Term.ZERO)) r.rest.push(ArrayTerm.buildNoClone(new Term(rest.length-i-1+""),rest[i]));
      }
      r.one=o>=2?rest[rest.length-2]:ZeroTerm.build();
      r.zero=o>=1?rest[rest.length-1]:ZeroTerm.build();
    }else{
      r.rest=[];
      for (var i=0;i<rest.length;i++){
        if (rest[i] instanceof ArrayTerm) r.rest.push(rest[i]);
        else if (!rest[i].equal(Term.ZERO)) r.rest.push(ArrayTerm.buildNoClone(new Term(rest.length-i+1+""),rest[i]));
      }
      r.one=one;
      r.zero=zero;
    }
  }else{
    if (typeof one=="undefined"){
      r.rest=[];
      r.one=Term.ZERO.clone();
      r.zero=rest;
    }else{
      r.rest=[];
      r.one=rest;
      r.zero=one;
    }
  }
  return r;
}
ArrayTerm.prototype=Object.create(Term.prototype);
ArrayTerm.prototype.clone=function (){
  return ArrayTerm.build(this.rest,this.one,this.zero);
}
ArrayTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    var r="";
    if (this.rest.length){
      /** @type {boolean} */
      var inlineShort=abbreviate===true||abbreviate["tf["]||abbreviate["f["]&&this.rest.length&&this.rest[0].rest.length==0&&isNat(this.rest[0].one);
      var hasInlined=false;
      for (var i=0,j=NaN;i<this.rest.length;i++){
        if (inlineShort){
          if (this.rest[i].rest.length==0&&isNat(this.rest[i].one)){
            var k=toNat(this.rest[i].one);
            if (!isNaN(j)&&j-1<k||k<2){
              inlineShort=false;
              i=-1;
              r="";
            }else{
              if (!isNaN(j)&&j-1!=k) r+="0,".repeat(j-k-1);
              j=k;
              r+=this.rest[i].zero.toString(abbreviate)+",";
              hasInlined=true;
            }
          }else if (hasInlined){
            inlineShort=false;
            i=-1;
            r="";
          }else r+="("+this.rest[i].toString(abbreviate)+"),";
        }else r+="("+this.rest[i].toString(abbreviate)+"),";
      }
      if (inlineShort&&!isNaN(j)&&j-1!=1) r+="0,".repeat(j-1-1);
    }
    return r+this.one.toString(abbreviate)+","+this.zero.toString(abbreviate);
  }else{
    if (this.rest.length) return this.rest.map(function (t){return "("+t.toString(abbreviate)+")";}).join(",")+","+this.one.toString(abbreviate)+","+this.zero.toString(abbreviate);
    else return this.one.toString(abbreviate)+","+this.zero.toString(abbreviate);
  }
}
ArrayTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=new Term(other);
  return other instanceof ArrayTerm&&this.rest.length==other.rest.length&&this.rest.every(function (e,i){return e.equal(other.rest[i]);})&&this.one.equal(other.one)&&this.zero.equal(other.zero);
}
/** @returns {Term&ArrayTerm} */
ArrayTerm.prototype.getLeft=function (){
  if (this.rest.length) return this.rest[0];
  else throw Error("getLeft() is not defined for "+this);
}
/** @returns {Term&ArrayTerm} */
ArrayTerm.prototype.getNotLeft=function (){
  if (this.rest.length) return ArrayTerm.buildNoClone(this.rest.slice(1),this.one,this.zero);
  else throw Error("getNotLeft() is not defined for "+this);
}
Object.defineProperty(ArrayTerm.prototype,"constructor",{
  value:ArrayTerm,
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
 * @param {number} end 
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

Term.ZERO=new Term("()");
Term.ONE=new Term("四(0)");
Term.SMALLOMEGA=new Term("四(1)");
Term.LARGEOMEGA=new Term("四_1(0)");
Term.M=new Term("四((1,0,1),0,0)");

/** @returns {boolean} */
function inT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return true; //1
  if (t instanceof FourTerm) return inDT(t.inner); //2
  if (t instanceof SumTerm) return t.terms.every(function (s){return !s.equal("0")&&inT(s);}); //3
  return false;
}
function inDT(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  return t instanceof ArrayTerm&&t.rest.every(inDT)&&inT(t.one)&&inT(t.zero);
}
/**
 * @param {Term} t
 * @param {(value:Term,index:number,array:Term[])=>boolean} f
 */
function isSumAndTermsSatisfy(t,f){
  return t instanceof SumTerm&&t.terms.every(f);
}
function isNat(t){
  try{
    if (!(t instanceof Term)) t=new Term(t);
  }catch(e){
    return false;
  }
  return t instanceof Term&&(t.equal(Term.ONE)||isSumAndTermsSatisfy(t,equalFunc(Term.ONE)));
}
function toNat(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!isNat(X)) throw Error("Invalid argument: "+X);
  if (X instanceof ZeroTerm) return 0;
  if (X instanceof FourTerm) return 1;
  if (X instanceof SumTerm) return X.terms.length;
  throw Error("This should be unreachable");
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
function lessThanOrEqualT(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  return equal(S,T)||lessThanT(S,T);
}
/**
 * @param {Term|string} S 
 * @param {Term|string} T 
 * @returns {boolean} S<T
 */
function lessThanT(S,T){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(T instanceof Term)) T=new Term(T);
  if (!inT(S)||!inT(T)) throw Error("Invalid argument: "+S+","+T);
  if (T instanceof ZeroTerm) return false; //1
  if (S instanceof ZeroTerm) return true; //2
  if (S instanceof FourTerm){ //3
    if (T instanceof FourTerm) return lessThanDT(S.inner,T.inner); //3.1
    if (T instanceof SumTerm) return lessThanOrEqualT(S,T.getLeft()); //3.2
  }
  if (S instanceof SumTerm){ //4
    if (T instanceof FourTerm) return lessThanT(S.getLeft(),T); //4.1
    if (T instanceof SumTerm) return bracketLessThanT(S.getLeft(),S.getNotLeft(),T.getLeft(),T.getNotLeft()); //4.2
  }
  throw Error("No rule to compute if "+S+"<"+T);
}
/**
 * @param {Term|string} S0 
 * @param {Term|string} S1 
 * @param {Term|string} T0 
 * @param {Term|string} T1 
 * @returns {boolean} [S0,S1]<[T0,T1]
 */
function bracketLessThanT(S0,S1,T0,T1){
  if (!(S0 instanceof Term)) S0=new Term(S0);
  if (!(S1 instanceof Term)) S1=new Term(S1);
  if (!(T0 instanceof Term)) T0=new Term(T0);
  if (!(T1 instanceof Term)) T1=new Term(T1);
  if (!inT(S0)||!inT(S1)||!inT(T0)||!inT(T1)) throw Error("Invalid argument: "+S0+","+S1+","+T0+","+T1);
  return lessThanT(S0,T0) //1
    ||equal(S0,T0)&&lessThanT(S1,T1); //2
    //3
  throw Error("No rule to compute if ["+S0+","+S1+"]<["+T0+","+T1+"]");
}
/**
 * @param {Term|string} X 
 * @param {Term|string} Y 
 * @returns X<=Y
 */
function lessThanOrEqualDT(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  return equal(X,Y)||lessThanDT(X,Y);
}
/**
 * @param {Term|string} X 
 * @param {Term|string} Y 
 * @returns {boolean} X<Y
 */
function lessThanDT(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  if (!(X instanceof ArrayTerm)||!inDT(X)||!(Y instanceof ArrayTerm)||!inDT(Y)) throw Error("Invalid argument: "+X+","+Y);
  if (Y.rest.length==0){ //1
    if (X.rest.length==0) return bracketLessThanT(X.one,X.zero,Y.one,Y.zero); //1.1
    else return false; //1.2
  }else{ //2
    if (X.rest.length==0) return true; //2.1
    else return bracketLessThanDT(X.getLeft(),X.getNotLeft(),Y.getLeft(),Y.getNotLeft()); //2.2
  }
  throw Error("No rule to compute if "+X+"<"+Y);
}
/**
 * @param {Term|string} X0 
 * @param {Term|string} X1 
 * @param {Term|string} Y0 
 * @param {Term|string} Y1 
 * @returns {boolean} [X0,X1]<[Y0,Y1]
 */
function bracketLessThanDT(X0,X1,Y0,Y1){
  if (!(X0 instanceof Term)) X0=new Term(X0);
  if (!(X1 instanceof Term)) X1=new Term(X1);
  if (!(Y0 instanceof Term)) Y0=new Term(Y0);
  if (!(Y1 instanceof Term)) Y1=new Term(Y1);
  if (!(X0 instanceof ArrayTerm)||!inDT(X0)||!(X1 instanceof ArrayTerm)||!inDT(X1)||!(Y0 instanceof ArrayTerm)||!inDT(Y0)||!(Y1 instanceof ArrayTerm)||!inDT(Y1)) throw Error("Invalid argument: "+X0+","+X1+","+Y0+","+Y1);
  return lessThanDT(X0,Y0) //1
    ||equal(X0,Y0)&&lessThanDT(X1,Y1); //2
    //3
  throw Error("No rule to compute if ["+X0+","+X1+"]<["+Y0+","+Y1+"]");
}
/**
 * Interpreting X as an extension of transfinitary array, return the value at index 0
 * @param {Term|string} X 
 * @returns {string} 零位(X)
 */
function getZero(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  return X.zero+"";
  throw Error("No rule to compute 零位("+X+")");
}
/**
 * Interpreting X as an extension of transfinitary array, set the value at index 0 to T
 * @param {Term|string} X 
 * @param {Term|string} T 
 * @returns {string} 零位変更(X,T)
 */
function setZero(X,T){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(T instanceof Term)) T=new Term(T);
  if (!(X instanceof ArrayTerm)||!inDT(X)||!inT(T)) throw Error("Invalid argument: "+X+","+T);
  if (X.rest.length) return X.rest.map(function (t){return "("+t+")";}).join(",")+","+X.one+","+T;
  else return X.one+","+T;
  throw Error("No rule to compute 零位変更("+X+","+T+")");
}
/**
 * Interpreting X as an extension of transfinitary array, set the value at index Y to T
 * @param {Term|string} X 
 * @param {Term|string} Y 
 * @param {Term|string} T 
 * @returns {string} 成分変更(X,Y,T)
 */
function set(X,Y,T){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  if (!(T instanceof Term)) T=new Term(T);
  if (!(X instanceof ArrayTerm)||!inDT(X)||!(Y instanceof ArrayTerm)||!inDT(Y)||!inT(T)) throw Error("Invalid argument: "+X+","+Y+","+T);
  if (equal(getZero(Y),Term.ZERO)){ //1
    if (X.rest.length==0){ //1.1
      if (equal(Y,"0,0")) return X.one+","+T; //1.1.1
      else if (equal(Y,"1,0")) return T+","+X.zero; //1.1.2
      else{ //1.1.3
        if (equal(T,Term.ZERO)) return X+""; //1.1.3.1
        else return "("+setZero(Y,T)+"),"+X; //1.1.3.2
      }
    }else{ //1.2
      var z0=X.getLeft();
      var z1=X.getNotLeft();
      var setZero_z0=setZero(z0,Term.ZERO);
      var Term_setZero_z0=new Term(setZero_z0);
      if (lessThanDT(Y,Term_setZero_z0)) return "("+z0+"),"+set(z1,Y,T); //1.2.1
      else if (equal(Term_setZero_z0,Y)){ //1.2.2
        if (equal(T,Term.ZERO)) return z1+""; //1.2.2.1
        else return "("+setZero(z0,T)+"),"+z1; //1.2.2.2
      }else{ //1.2.3
        if (equal(T,Term.ZERO)) return X+""; //1.2.3.1
        else return "("+setZero(Y,T)+"),"+X; //1.2.3.2
      }
    }
  }else return set(X,setZero(Y,Term.ZERO),T); //2
  throw Error("No rule to compute 成分変更("+X+","+Y+","+T+")");
}
/**
 * Interpreting X as an extension of transfinitary array, get the rightmost nonzero element, but 0 if none exists
 * @param {Term|string} X 
 * @returns {string|0} 右端(X)
 */
function getRightmostNonzero(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  if (!equal(X.zero,Term.ZERO)) return Term.ZERO+","+X.zero; //1.1;2.3
  else if (!equal(X.one,Term.ZERO)) return Term.ONE+","+X.one; //1.2;2.3
  else if (X.rest.length==0) return 0; //1.3
  else{
    for (var i=X.rest.length-1;i>=0;i--){
      if (!equal(getZero(X.rest[i]),Term.ZERO)) return X.rest[i]+""; //2.2
    }
    return 0; //2.1
  }
  throw Error("No rule to compute 右端("+X+")");
}
/**
 * Interpreting X as an extension of transfinitary array, set 1 in place of the rightmost nonzero value
 * @param {Term|string} X 
 * @param {Term|string} T 
 * @returns {string} 右端成分変更(X,T)
 */
function setRightmostNonzero(X,T){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(T instanceof Term)) T=new Term(T);
  if (!(X instanceof ArrayTerm)||!inDT(X)||!inT(T)) throw Error("Invalid argument: "+X+","+T);
  var getRightmostNonzero_X=getRightmostNonzero(X);
  if (getRightmostNonzero_X===0) return Term.ZERO+","+Term.ZERO; //1
  else return set(X,getRightmostNonzero_X,T); //2
  throw Error("No rule to compute 右端成分変更("+X+","+T+")");
}
/**
 * Interpreting X as an extension of transfinitary array, if setting 0 in place of the rightmost nonzero value would result in a nonzero array, return the nonzero array, otherwise recurse inside the entry
 * @param {Term|string} X 
 * @returns {string} 右端縮小(X,T)
 */
function shrinkRightmostNonzero(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  var getRightmostNonzero_X=getRightmostNonzero(X);
  if (getRightmostNonzero_X===0) return Term.ZERO+","+Term.ZERO; //1
  else{ //2
    if (equal(getZero(getRightmostNonzero_X),Term.ONE)){ //2.1
      if (X.rest.length&&X.rest[0].rest.length&&equal(X.one,Term.ZERO)&&equal(X.zero,Term.ZERO)){ //2.1.1
        var X_getLeft=X.getLeft();
        var z0=X_getLeft.getLeft();
        var z1=X_getLeft.getNotLeft();
        return setZero(shrinkRightmostNonzero("("+z0+"),"+setZero(z1,Term.ZERO)),Term.ONE);
      }else return setRightmostNonzero(X,Term.ZERO); //2.1.2
    }else return setRightmostNonzero(X,Term.ONE); //2.2
  }
  throw Error("No rule to compute 右端縮小("+X+")");
}
/**
 * Get the maximum element of array recursively
 * @param {Term|string} X 
 * @returns {string} 出現項上限(X)
 */
function maximumElement(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  return X.rest.reduce(function (a,t){var b=maximumElement(t);return lessThanT(a,b)?new Term(b):a;},lessThanT(X.zero,X.one)?X.one:X.zero)+"";
  throw Error("No rule to compute 出現項上限("+X+")");
}
/**
 * Get the maximum value nonrecursively
 * @param {Term|string} X 
 * @returns {string} 成分上限(X)
 */
function maximumEntry(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  return X.rest.reduce(function (a,t){return lessThanT(a,t.zero)?t.zero:a;},lessThanT(X.zero,X.one)?X.one:X.zero)+"";
  throw Error("No rule to compute 成分上限("+X+")");
}
/**
 * Interpreting X and Y as extensions of transfinitary array, decides whether there is an initial segment of X that is also an initial segment of Y, such that the maximum element of the rest of X is less than the value of the rightmost nonzero entry of Y.
 * @param {Term|string} X 
 * @param {Term|string} Y 
 * @returns {boolean} XがYに埋め込み可能
 */
function embeddable(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  if (!(X instanceof ArrayTerm)||!inDT(X)||!(Y instanceof ArrayTerm)||!inDT(Y)) throw Error("Invalid argument: "+X+","+Y);
  var maximumEntry_X=maximumEntry(X);
  var Term_maximumEntry_X=new Term(maximumEntry_X);
  var maximumEntry_Y=maximumEntry(Y);
  var Term_maximumEntry_Y=new Term(maximumEntry_Y);
  if (lessThanT(Term_maximumEntry_X,Term_maximumEntry_Y)) return true; //1
  else if (equal(Term_maximumEntry_X,Term_maximumEntry_Y)){ //2
    if (X.rest.length==0) //2.1
      return Y.rest.length==0&&equal(X.one,Y.one) //2.1.1
        &&lessThanT(X.zero,Y.zero); //2.1.2
    else //2.2
      return Y.rest.length&&equal(X.getLeft(),Y.getLeft()) //2.2.1
        &&embeddable(X.getNotLeft(),Y.getNotLeft()); //2.2.2
  }else return false; //3
  throw Error("No rule to compute whether "+X+"が"+Y+"に埋め込み可能");
}
/**
 * @param {Term|string} X 
 * @param {Term|string} Y 
 * @returns {boolean} XがY未満で構成可能
 */
function constructibleDT(X,Y){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(Y instanceof Term)) Y=new Term(Y);
  if (!(X instanceof ArrayTerm)||!inDT(X)||!(Y instanceof ArrayTerm)||!inDT(Y)) throw Error("Invalid argument: "+X+","+Y);
  var maximumElement_X=maximumElement(X);
  var Term_maximumElement_X=new Term(maximumElement_X);
  var maximumElement_Y=maximumElement(Y);
  var Term_maximumElement_Y=new Term(maximumElement_Y);
  if (lessThanOrEqualT(Term_maximumElement_X,Term_maximumElement_Y)){ //1
    if (X.rest.length==0) //1.1
      return constructibleT(X.one,Y) //1.1.1
        &&constructibleT(X.zero,Y); //1.1.2
    else //1.2
      return constructibleDT(X.getLeft(),Y) //1.2.1
        &&constructibleDT(X.getNotLeft(),Y); //1.2.2
  }else return false; //2
  throw Error("No rule to compute whether "+X+"が"+Y+"未満で構成可能");
}
/**
 * @param {Term|string} S 
 * @param {Term|string} Y 
 * @returns {boolean} SがY未満で構成可能
 */
function constructibleT(S,Y){
  if (!(S instanceof Term)) S=new Term(S);
  if (!(Y instanceof Term)) Y=new Term(Y);
  if (!inT(S)||!(Y instanceof ArrayTerm)||!inDT(Y)) throw Error("Invalid argument: "+S+","+Y);
  if (getRightmostNonzero(Y)===0) return equal(S,Term.ZERO); //1
  else{ //2
    if (lessThanT(S,"四("+setRightmostNonzero(Y,Term.ONE)+")")) return true; //2.1
    else{ //2.2
      if (S instanceof FourTerm){ //2.2.1
        var x=S.inner;
        return constructibleDT(x,Y) //2.2.1.1
          &&(!equal(maximumElement(x),maximumElement(Y))||embeddable(x,Y)); //2.2.1.2
      }else //2.2.2
        return S instanceof SumTerm //2.2.2.1
          &&constructibleT(S.getLeft(),Y) //2.2.2.2
          &&constructibleT(S.getNotLeft(),Y); //2.2.2.3
    }
  }
  throw Error("No rule to compute whether "+S+"が"+Y+"未満で構成可能");
}
/**
 * @param {Term|string} X 
 * @returns {boolean} Xの各引数が自身で構成可能である
 */
function entriesSelfConstructible(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  return X.rest.every(function (z0){var Term_setZero_z0_1_00=new Term("("+setZero(z0,Term.ONE)+"),0,0");return constructibleDT(Term_setZero_z0_1_00,Term_setZero_z0_1_00);});
  throw Error("No rule to compute whether "+X+"の各引数が自身で構成可能である");
}
/**
 * Returns whether X is in reduced form: interpreting X as an extension of transfinitary array, it is true iff there are no redundant entries noting a 0 and the entries are in order
 * @param {Term|string} X 
 * @returns {boolean} Xが簡約
 */
function isReduced(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  if (X.rest.length==0) return true; //1
  for (var i=X.rest.length-1,Term_setZero_z2_0=new Term("1,0");i>=0;i--){ //2
    var z0=X.rest[i];
    if (!isReduced(z0)||equal(getZero(z0),Term.ZERO)) return false; //2.1;2.3
    var Term_setZero_z0_0=new Term(setZero(z0,Term.ZERO));
    if (!lessThanDT(Term_setZero_z2_0,Term_setZero_z0_0)) return false; //2.4
    Term_setZero_z2_0=Term_setZero_z0_0;
  }
  return true;
  throw Error("No rule to compute whether "+X+"が簡約");
}
/**
 * Returns whether S is standard
 * @param {Term|string} S 
 * @returns {boolean} Sが標準形
 */
function isStandardT(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)) throw Error("Invalid argument: "+S);
  if (S instanceof ZeroTerm) return true; //1
  if (S instanceof FourTerm){ //2
    var x=S.inner;
    return constructibleDT(x,x) //2.1
      &&isStandardDT(x); //2.2
  }
  if (S instanceof SumTerm){ //3;4
    for (var i=0;i<S.terms.length;i++){
      if (!isStandardT(S.terms[i])) return false; //3.1;3.2
      if (i!=S.terms.length-1&&!lessThanOrEqualT(S.terms[i+1],S.terms[i])) return false; //3.3
    }
    return true;
  }
  throw Error("No rule to compute whether "+S+"が標準形");
}
/**
 * Returns whether X is standard
 * @param {Term|string} X 
 * @returns {boolean} Xの各引数が標準形
 */
function entriesStandard(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  return X.rest.every(entriesStandard)&&isStandardT(X.one)&&isStandardT(X.zero);
  throw Error("No rule to compute whether "+X+"の各引数が標準形");
}
/**
 * Returns whether X is standard
 * @param {Term|string} X 
 * @returns {boolean} Xが標準形
 */
function isStandardDT(X){
  if (!(X instanceof Term)) X=new Term(X);
  if (!(X instanceof ArrayTerm)||!inDT(X)) throw Error("Invalid argument: "+X);
  if (equal(X,Term.ZERO+","+Term.ZERO)) return true; //1
  else //2
    return isReduced(X) //2.1
      &&entriesStandard(X) //2.2
      &&entriesSelfConstructible(X) //2.3
      &&isStandardT("四("+shrinkRightmostNonzero(X)+")"); //2.4
  throw Error("No rule to compute whether "+X+"が標準形");
}
/**
 * @param {Term|string} S 
 * @returns {boolean} S∈OT
 */
function inOT(S){
  return isStandardT(S);
}
/**
 * Length of S as a string
 * @param {Term|string} S
 * @returns {number} 字数(S)
 */
function charLength(S){
  if (!(S instanceof Term)) S=new Term(S);
  if (S instanceof ZeroTerm) return 2;
  if (S instanceof FourTerm) return 3+charLength(S.inner);
  if (S instanceof SumTerm) return S.terms.reduce(function(a,t){return a+charLength(t);},S.terms.length-1);
  if (S instanceof ArrayTerm) return S.rest.reduce(function (a,t){return a+charLength(t);},charLength(S.one)+charLength(S.zero)+S.rest.length*3+1);
  throw Error("No rule to compute whether 字数("+S+")");
}
/**
 * Fundamental sequence by naively searching for every term within the length limit
 * @param {Term|string} S 
 * @param {number} n 
 * @returns {string} S[T]
 */
function fundNaive(S,n){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)||typeof n!="number") throw Error("Invalid argument: "+S+","+n);
  var maxLength=charLength(S)+9*n;
  var shortestTermLength=2; //()
  var shortestNonzeroTermLength=8; //四((),())
  var shortestArrayLength=5; //(),()
  var t=Term.ZERO;
  /** @type {string[][]} */
  var termsByLength=[null,null,[Term.ZERO+""],null,null];
  /** @type {string[][]} */
  var principalTermsByLength=[null,null,null,null,null];
  /** @type {string[][]} */
  var arraysByLength=[null,null,null,null,null];
  for (var i=5;i<=maxLength;i++){
    termsByLength[i]=[];
    principalTermsByLength[i]=[];
    if (arraysByLength[i-3]){
      for (var j=0;j<arraysByLength[i-3].length;j++){
        var newTerm="四("+arraysByLength[i-3][j]+")";
        // console.log(newTerm);
        var parsedNewTerm=new Term(newTerm);
        if (isStandardT(parsedNewTerm)){
          termsByLength[i].push(newTerm);
          principalTermsByLength[i].push(newTerm);
          if (lessThanT(t,parsedNewTerm)&&lessThanT(parsedNewTerm,S)){
            t=parsedNewTerm;
            console.log(newTerm);
          }
        }
      }
    }
    for (var j=shortestNonzeroTermLength;j<=i-shortestNonzeroTermLength-1;j++){
      if (principalTermsByLength[j]&&termsByLength[i-j-1]){
        for (var k=0;k<principalTermsByLength[j].length;k++){
          for (var l=0;l<termsByLength[i-j-1].length;l++){
            var newTerm=principalTermsByLength[j][k]+"+"+termsByLength[i-j-1][l];
            // console.log(newTerm);
            var parsedNewTerm=new Term(newTerm);
            if (isStandardT(parsedNewTerm)){
              termsByLength[i].push(newTerm);
              if (lessThanT(t,parsedNewTerm)&&lessThanT(parsedNewTerm,S)){
                t=parsedNewTerm;
                console.log(newTerm);
              }
            }
          }
        }
      }
    }
    if (i<=maxLength-3){ //The shortest use of array x is 四(x)
      arraysByLength[i]=[];
      for (var j=shortestTermLength;j<=i-shortestTermLength-1;j++){
        if (termsByLength[j]&&termsByLength[i-j-1]){
          for (var k=0;k<termsByLength[j].length;k++){
            for (var l=0;l<termsByLength[i-j-1].length;l++){
              var newArray=termsByLength[j][k]+","+termsByLength[i-j-1][l];
              // console.log(newArray);
              var parsedNewArray=new Term(newArray);
              if (isStandardDT(parsedNewArray)) arraysByLength[i].push(newArray);
            }
          }
        }
      }
      for (var j=shortestArrayLength;j<=i-shortestArrayLength-3;j++){
        if (arraysByLength[j]&&arraysByLength[i-j-3]){
          for (var k=0;k<arraysByLength[j].length;k++){
            for (var l=0;l<arraysByLength[i-j-3].length;l++){
              var newArray="("+arraysByLength[j][k]+"),"+arraysByLength[i-j-3][l];
              // console.log(newArray);
              var parsedNewArray=new Term(newArray);
              if (isStandardDT(parsedNewArray)) arraysByLength[i].push(newArray);
            }
          }
        }
      }
    }
    console.log(i+"/"+maxLength);
  }
  return t+"";
}
/**
 * List all standard terms within the length limit
 * @param {number} maxLength 
 * @returns {string[][][]}
 */
function generateStandardTerms(maxLength){
  var shortestTermLength=2; //()
  var shortestNonzeroTermLength=8; //四((),())
  var shortestArrayLength=5; //(),()
  var t=Term.ZERO;
  /** @type {string[][]} */
  var termsByLength=[null,null,[Term.ZERO+""],null,null];
  /** @type {string[][]} */
  var principalTermsByLength=[null,null,null,null,null];
  /** @type {string[][]} */
  var arraysByLength=[null,null,null,null,null];
  for (var i=5;i<=maxLength;i++){
    termsByLength[i]=[];
    principalTermsByLength[i]=[];
    if (arraysByLength[i-3]){
      for (var j=0;j<arraysByLength[i-3].length;j++){
        var newTerm="四("+arraysByLength[i-3][j]+")";
        // console.log(newTerm);
        var parsedNewTerm=new Term(newTerm);
        if (isStandardT(parsedNewTerm)){
          termsByLength[i].push(newTerm);
          principalTermsByLength[i].push(newTerm);
        }
      }
    }
    for (var j=shortestNonzeroTermLength;j<=i-shortestNonzeroTermLength-1;j++){
      if (principalTermsByLength[j]&&termsByLength[i-j-1]){
        for (var k=0;k<principalTermsByLength[j].length;k++){
          for (var l=0;l<termsByLength[i-j-1].length;l++){
            var newTerm=principalTermsByLength[j][k]+"+"+termsByLength[i-j-1][l];
            // console.log(newTerm);
            var parsedNewTerm=new Term(newTerm);
            if (isStandardT(parsedNewTerm)){
              termsByLength[i].push(newTerm);
            }
          }
        }
      }
    }
    if (i<=maxLength-3){ //The shortest use of array x is 四(x)
      arraysByLength[i]=[];
      for (var j=shortestTermLength;j<=i-shortestTermLength-1;j++){
        if (termsByLength[j]&&termsByLength[i-j-1]){
          for (var k=0;k<termsByLength[j].length;k++){
            for (var l=0;l<termsByLength[i-j-1].length;l++){
              var newArray=termsByLength[j][k]+","+termsByLength[i-j-1][l];
              // console.log(newArray);
              var parsedNewArray=new Term(newArray);
              if (isStandardDT(parsedNewArray)) arraysByLength[i].push(newArray);
            }
          }
        }
      }
      for (var j=shortestArrayLength;j<=i-shortestArrayLength-3;j++){
        if (arraysByLength[j]&&arraysByLength[i-j-3]){
          for (var k=0;k<arraysByLength[j].length;k++){
            for (var l=0;l<arraysByLength[i-j-3].length;l++){
              var newArray="("+arraysByLength[j][k]+"),"+arraysByLength[i-j-3][l];
              // console.log(newArray);
              var parsedNewArray=new Term(newArray);
              if (isStandardDT(parsedNewArray)) arraysByLength[i].push(newArray);
            }
          }
        }
      }
    }
    console.log(i+"/"+maxLength);
  }
  return [termsByLength,arraysByLength];
}
/**
 * Fundamental sequence by increasing standard terms starting from 0
 * @param {Term|string} S 
 * @param {number} n 
 * @returns {string} S[T]
 */
function fundSmart(S,n){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)||typeof n!="number") throw Error("Invalid argument: "+S+","+n);
  var maxLength=charLength(S)+9*n;
  var t=Term.ZERO;
  var currentLength=charLength(t);
  var UNDETERMINED=0;
  var INREST=1;
  var INONE=2;
  var INZERO=3;
  var INFOUR=4;
  var OMEGA_ONE=new Term(Term.SMALLOMEGA+","+Term.ONE);
  var TWO_ONE=new Term(Term.ONE+"+"+Term.ONE+","+Term.ONE);
  var LENGTH_ONE_MINUS_LENGTH_ZERO=charLength(Term.ONE)-charLength(Term.ZERO);
  var omegaOneCase=false;
  do{
    /** @type {{term:Term,method:number,}[]} */
    var scope=[{term:t,method:UNDETERMINED}];
    /** @param {Term} newTerm */
    function test(newTerm){
      var lengthDiff=charLength(newTerm)-charLength(scope[scope.length-1].term)-(omegaOneCase?LENGTH_ONE_MINUS_LENGTH_ZERO:0);
      if (currentLength+lengthDiff>maxLength) return false;
      for (var i=scope.length-2;i>=0;i--){
        var outTerm=scope[i].term;
        if (outTerm instanceof ArrayTerm){
          if (scope[i].method==INREST) newTerm=ArrayTerm.buildNoClone(outTerm.rest.slice(0,-1).concat([newTerm]),outTerm.one,outTerm.zero);
          else if (scope[i].method==INONE){
            var inFour=i+1>=2&&scope[i+1-2].method==INFOUR;
            var inArray=i+1>=2&&!inFour;
            var b=inArray?Term.ONE:Term.ZERO;
            newTerm=ArrayTerm.buildNoClone(outTerm.rest,newTerm,b);
          }else if (scope[i].method==INZERO) newTerm=ArrayTerm.buildNoClone(outTerm.rest,outTerm.one,newTerm);
        }else{
          if (scope[i].method==INFOUR){
            newTerm=FourTerm.buildNoClone(newTerm);
            if (outTerm instanceof SumTerm) newTerm=SumTerm.buildNoClone(outTerm.terms.slice(0,-1).concat([newTerm]));
          }
        }
      }
      // console.warn(newTerm);
      if (lessThanT(newTerm,S)&&isStandardT(newTerm)){
        console.log(newTerm+"");
        t=newTerm;
        currentLength+=lengthDiff;
        omegaOneCase=false;
        return true;
      }return false;
    }
    while (scope.length){
      var current=scope[scope.length-1];
      if (current.term instanceof ArrayTerm){
        var inOmegaOne=scope.length>=4&&scope[scope.length-2].method==INFOUR&&scope[scope.length-3].method==INONE&&scope[scope.length-4].method!=INFOUR&&equal(scope[scope.length-3].term,OMEGA_ONE);
        var inFour=scope.length>=2&&scope[scope.length-2].method==INFOUR;
        var inArray=scope.length>=2&&!inFour;
        var b=inArray?Term.ONE:Term.ZERO;
        if (current.method<=UNDETERMINED){
          if (current.term.rest.length&&equal(current.term.one,Term.ZERO)&&equal(current.term.zero,b)){
            current.method=INREST;
            scope.push({term:current.term.rest[current.term.rest.length-1],method:UNDETERMINED});
            continue;
          }
        }
        if (current.method<=INREST&&(inOmegaOne||equal(current.term.zero,b))){
          if (inOmegaOne||inFour&&equal(current.term.one,Term.ZERO)||inArray&&(current.term.rest.length==0&&equal(current.term.one,Term.SMALLOMEGA)||equal(current.term.one,Term.ZERO))){
            if (test(ArrayTerm.buildNoClone(current.term.rest.concat([OMEGA_ONE]),Term.ZERO,b))
              ||test(ArrayTerm.buildNoClone(current.term.rest.concat([TWO_ONE]),Term.ZERO,b))) break;
          }
          omegaOneCase=inOmegaOne;
          current.method=INONE;
          scope.push({term:current.term.one,method:UNDETERMINED});
          continue;
        }
        if (current.method<=INONE){
          omegaOneCase=!inOmegaOne&&omegaOneCase;
          current.method=INZERO;
          scope.push({term:current.term.zero,method:UNDETERMINED});
          continue;
        }
      }else{
        if (current.method<=INZERO){
          if (current.term instanceof FourTerm){
            current.method=INFOUR;
            scope.push({term:current.term.inner,method:UNDETERMINED});
            continue;
          }else if (current.term instanceof SumTerm){
            current.method=INFOUR;
            scope.push({term:current.term.terms[current.term.terms.length-1].inner,method:UNDETERMINED});
            continue;
          }
        }
        if (test(equal(current.term,Term.ZERO)?Term.ONE:SumTerm.buildNoClone([current.term,Term.ONE]))) break;
      }
      scope.pop();
    }
  }while(scope.length);
  return t+"";
  throw Error("No rule to compute "+S+"["+n+"]");
}
/**
 * Fundamental sequence
 * @param {Term|string} S 
 * @param {number} n 
 * @param {string=} method "naive": check for every term within the maximum length | "smart": incrementally increase from 0 through standard terms
 * @returns {string} S[T]
 */
function fund(S,n,method){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)||typeof n!="number") throw Error("Invalid argument: "+S+","+n);
  if (method=="naive") return fundNaive(S,n);
  if (!method||method=="smart") return fundSmart(S,n);
  throw Error("Unknown method: "+method);
}
var fundMethods=["naive","smart"];
/**
 * A variation on the fast-growing hierarchy
 * @param {Term|string} S 
 * @param {number} m 
 * @param {number} n 
 * @returns {number} S映m姫n
 */
function Eiki(S,m,n){
  if (!(S instanceof Term)) S=new Term(S);
  if (!inT(S)||typeof m!="number"||typeof n!="number") throw Error("Invalid argument: "+S+","+m+","+n);
  if (m==0) return n; //1
  else if (m==1){ //2
    if (equal(S,Term.ZERO)) return n+1; //2.1
    else return Eiki(fund(S,n),n,n); //2.2
  }else return Eiki(S,1,Eiki(S,m-1,n)); //3
}
/**
 * Limit of the notation
 * @param {number} n 
 * @returns {string} 季n
 */
function seasons(n){
  if (typeof n!="number") throw Error("Invalid argument: "+n);
  var r="四("+Term.ONE+"),"+Term.ONE;
  return n?"(".repeat(n)+r+("),"+r).repeat(n):r;
}
/**
 * Large function
 * @param {number} n 
 * @returns {number} n王
 */
function ruler(n){
  if (typeof n!="number") throw Error("Invalid argument: "+n);
  return Eiki("四("+seasons(n)+")",1,n);
}
/**
 * Large number
 * 
 * See also: https://en.touhouwiki.net/wiki/Phantasmagoria_of_Flower_View/Story/Eiki%27s_Scenario
 * @returns {number} 貴方がきちんと私の定義を理解しているか見に来たので数
 */
function ICameHereToSeeIfYouProperlyUnderstoodMyDefinitionNumber(){
  return ruler(ruler(ruler(ruler(ruler(ruler(ruler(ruler(ruler(ruler(10))))))))));
}

var functionsToWrap=[
  inT,
  inDT,
  equal,
  lessThanT,
  bracketLessThanT,
  lessThanDT,
  bracketLessThanDT,
  getZero,
  setZero,
  set,
  getRightmostNonzero,
  setRightmostNonzero,
  shrinkRightmostNonzero,
  maximumElement,
  maximumEntry,
  embeddable,
  constructibleDT,
  constructibleT,
  entriesSelfConstructible,
  isReduced,
  isStandardT,
  entriesStandard,
  isStandardDT,
  charLength
];
var memos=[];
function wrapFunction(f){
  var memo=new Map();
  memos.push(memo);
  var name=f.name;
  var length=f.length;
  var wrapper=function (){
    if (arguments.length==length){
      var key=Array.from(arguments).map(function (e){return e.toString();}).join(";");
      if (memo.has(key)) return memo.get(key);
      else{
        var result=f.apply(null,arguments);
        memo.set(key,result);
        return result;
      }
    }else return f.apply(null,arguments);
  }
  this["_"+name]=f;
  this[name]=wrapper;
  return wrapper;
}
function clearMemos(){
  memos.forEach(function (e){e.clear();});
}
functionsToWrap.forEach(wrapFunction);
setInterval(clearMemos,10000);
function undoWrap(){
  functionsToWrap.forEach(function (f){
    var name=f.name;
    this[name]=this["_"+name];
    this["_"+name]=undefined;
  });
}

/** @type {[string,number][]} */
var testTermsPre=[
  ["0",-1],
  ["1",-1],
  ["ω",3],
  ["ω+ω",3],
  ["四(2)",3],
  ["四(ω)",3],
  ["四(Ω)",2],
  ["四(Ω+Ω)",3],
  ["四(四_1(1))",3],
  ["四(四_1(四(Ω)))",2],
  ["四(四_1(Ω))",4],
  ["四(四_2(0))",2],
  ["四(四_2(0)+四(四_2(0)))",2],
  ["四(四_2(0)+四_1(0))",-1],
  ["四(四_2(0)+四_1(四_2(0)))",1],
  ["四(四_2(0)+四_2(0))",6],
  ["四(四_3(0))",4],
  ["四(四_ω(0))",3],
  ["四(四_Ω(0))",3],
  ["四(四_Ω(0)+四_1(四_Ω(0)))",2],
  ["四(四(1,0,0))",0],
  ["四(四(1,0,0)+四_1(四(1,0,0)))",0],
  ["四(四(1,0,0)+四_四(1,0,0)(0))",0],
  ["四(四(1,0,0)+四_四(1,0,0)(1))",5],
  ["四(四(1,0,0)+四_四(1,0,0)(四(1,0,0)))",6],
  ["四(四(1,0,0)+四_四(1,0,0)+1(0))",8],
  ["四(四(1,0,0)+四(1,0,0))",7],
  ["四(四(1,0,1))",4],
  ["四(四(1,0,Ω))",-1],
  ["四(四(1,0,四_四(1,0,0)(0)))",0],
  ["四(四(1,0,四_四(1,0,0)(1)))",-1],
  ["四(四(1,0,四_四(1,0,1)(0)))",4],
  ["四(四(1,0,四(1,0,0)))",6],
  ["四(四(1,0,四(1,0,0)+四(1,0,0)))",-1],
  ["四(四(1,1,0))",4],
  ["四(四(1,1,0)+四_1(四(1,1,0)))",4],
  ["四(四(1,1,0)+四_四(1,1,0)(0))",4],
  ["四(四(1,1,0)+四_四(1,1,0)+1(0))",-1],
  ["四(四(1,1,0)+四_四(1,1,0)+1(1))",-1],
  ["四(四(1,1,0)+四(1,0,0))",-1],
  ["四(四(1,1,0)+四(1,0,四(1,1,0)))",4],
  ["四(四(1,1,0)+四(1,1,0))",9],
  ["四(四(1,Ω,0))",4],
  ["四(四(1,四(1,0,0),0))",6],
  ["四(四(2,0,0))",4],
  ["四(四(2,0,0)+四_四(1,0,0)(四(2,0,0)))",4],
  ["四(四(2,0,0)+四_四(2,0,0)(0))",4],
  ["四(四(2,0,0)+四(1,四(2,0,0),0))",4],
  ["四(四(2,0,0)+四(2,0,0))",9],
  ["四(四(3,0,0))",-1],
  ["四(四(ω,0,0))",-1],
  ["四(四(Ω,0,0))",-1],
  ["四(四(四(1,0,0),0,0))",-1],
  ["四(四(1,0,0,0))",3],
  ["四(四((ω,1),0,0))",3],
  ["四(四((ω,1),0,0)+四_1(四((ω,1),0,0)))",3],
  ["四(四((ω,1),0,0)+四_四((ω,1),0,0)(0))",3],
  ["四(四((ω,1),0,0)+四(1,四((ω,1),0,0),0))",3],
  ["四(四((ω,1),0,0)+四(四((ω,1),0,0),0,0))",3],
  ["四(四((ω,1),0,0)+四((ω,1),0,0))",3],
  ["四(四((ω,1),0,1))",-1],
  ["四(四((ω,1),1,0))",3],
  ["四(四((ω,2),0,0))",4],
  ["四(四((ω,ω),0,0))",-1],
  ["四(四((ω+1,1),0,0))",3],
  ["四(四((ω+1,1),0,0)+四((ω+1,1),0,0))",7],
  ["四(四((Ω,1),0,0))",4],
  ["四(四((Ω,2),0,0))",8],
  ["四(四((四((ω,1),0,0),1),0,0))",3],
  ["四(四((四((ω,1),0,0),2),0,0))",-1],
  ["四(M)",3],
  ["四(M+四_1(M))",3],
  ["四(M+四_M(0))",3],
  ["四(M+四_M(M))",10],
  ["四(M+四(1,0,0))",4],
  ["四(M+四(M,0,0))",-1],
  ["四(M+四((ω,M),0,0))",-1],
  ["四(M+四((M,1),0,0))",3],
  ["四(M+四((M,1),0,1))",-1],
  ["四(M+四((M,1),0,四((M,1),0,0)))",3],
  ["四(M+四((M,1),0,四((M,1),1,0)))",7],
  ["四(M+四((M,1),0,四((M,2),0,0)))",9],
  ["四(M+四((M,1),0,M))",10],
  ["四(M+四((M,1),1,0))",13],
  ["四(M+四((M,1),四((M,1),0,0),0))",-1],
  ["四(M+四((M,1),四((M,1),(2,1),0,0),0))",-1],
  ["四(M+四((M,1),M,0))",-1],
  ["四(M+四((M,1),(2,1),0,0))",-1],
  ["四(M+四((M,1),(2,四((M,1),0,0)),0,0))",-1],
  ["四(M+四((M,1),(ω,1),0,0))",2],
  ["四(M+四((M,2),0,0))",9],
  ["四(M+四((M,ω),0,0))",-1],
  ["四(M+四((M,四((M,1),0,0)),0,0))",-1],
  ["四(M+四((M,M),0,0))",3],
  ["四(M+四((M+1,1),0,0))",13],
  ["四(M+四((M+1,1),(M,1),0,0))",3],
  ["四(M+四((M+1,1),(M,四((M+1,2),0,0)),0,0))",6],
  ["四(M+四((M+1,1),(M,M),0,0))",12],
  ["四(M+四((M+1,2),0,0))",-1],
  ["四(M+四((M+四((M,1),0,0),1),0,0))",-1],
  ["四(M+M)",12],
  ["四(四((1,0,1),0,1))",11],
  ["四(四((1,0,1),0,1)+四_1(M))",-1],
  ["四(四((1,0,1),0,1)+四_1(M+M))",4],
  ["四(四((1,0,1),0,1)+四_M(M))",-1],
  ["四(四((1,0,1),0,1)+四_四((1,0,1),0,1)(M))",14],
  ["四(四((1,0,1),0,1)+四_四((1,0,1),0,1)(M+M))",-1],
  ["四(四((1,0,1),0,1)+四((M,1),0,M))",10],
  ["四(四((1,0,1),0,1)+四((M,2),0,0))",-1],
  ["四(四((1,0,1),0,1)+四((四((1,0,1),0,1),1),0,M))",11],
  ["四(四((1,0,1),0,1)+M)",4],
  ["四(四((1,0,1),0,M))",4],
  ["四(四((1,0,1),0,四((1,0,1),0,1)))",-1],
  ["四(四((1,0,1),1,0))",6],
  ["四(四((1,0,1),1,0)+四((四((1,0,1),1,0),1),0,M))",-1],
  ["四(四((1,0,1),1,0)+四((四((1,0,1),1,0),1),0,四((1,0,1),1,0)))",6],
  ["四(四((1,0,1),1,0)+四((四((1,0,1),1,0),2),0,0))",13],
  ["四(四((1,0,1),ω,0))",-1],
  ["四(四((1,0,1),M,0))",-1],
  ["四(四((1,0,1),(2,1),0,0))",-1],
  ["四(四((1,0,1),(ω,1),0,0))",-1],
  ["四(四((1,0,1),(M,1),0,0))",3],
  ["四(四((1,0,1),(四((1,0,1),(M,1),0,0),1),0,0))",-1],
  ["四(四((1,0,2),0,0))",9],
  ["四(四((1,1,1),0,0))",10],
  ["四(四((1,四((M,1),0,0),1),0,0))",-1], //* Probably no longer nonstandard
  ["四(四((1,M,1),0,0))",4],
  ["四(四((2,0,1),0,0))",6],
  ["四(四((2,0,1),0,0)+四((M,四((2,0,1),0,0)),0,0))",6],
  ["四(四((2,0,1),0,0)+四((M,四((2,0,1),0,0)),0,M))",15],
  ["四(四((2,0,1),0,0)+四((M,四((2,0,1),0,0)),0,四((2,0,1),0,0)))",17],
  ["四(四((2,0,1),0,0)+四((四((2,0,1),0,0),1),0,0))",6],
  ["四(四((2,0,1),0,0)+四((四((2,0,1),0,0),1),0,M))",12],
  ["四(四((2,0,1),0,0)+四((四((2,0,1),0,0),1),0,四((2,0,1),0,0)))",17],
  ["四(四((2,0,1),0,0)+四((四((2,0,1),0,0),1),(M,1),0,0))",3],
  ["四(四((2,0,1),0,0)+四((四((2,0,1),0,0),M),0,0))",12],
  ["四(四((2,0,1),0,0)+四((四((2,0,1),0,0),四((2,0,1),0,0)),0,0))",17],
  ["四(四((2,0,1),0,0)+M)",-1],
  ["四(四((2,0,1),0,0)+四((1,0,1),0,四((2,0,1),0,0)))",-1],
  ["四(四((2,0,1),0,0)+四((1,0,1),(M,1),0,0))",-1],
  ["四(四((2,0,1),0,0)+四((1,0,1),(四((2,0,1),0,0),1),0,0))",10],
  ["四(四((2,0,1),0,0)+四((1,0,2),0,0))",-1],
  ["四(四((2,0,1),0,0)+四((1,0,四((2,0,1),0,0)),0,0))",6],
  ["四(四((2,0,1),0,0)+四((1,0,四((2,0,1),0,0)),0,四((2,0,1),0,0)))",12],
  ["四(四((2,0,1),0,0)+四((1,0,四((2,0,1),0,0)),(四((2,0,1),0,0),1),0,0))",10],
  ["四(四((2,0,1),0,0)+四((1,M,1),0,0))",10],
  ["四(四((2,0,1),0,0)+四((1,四((2,0,1),0,0),1),0,0))",6],
  ["四(四((2,0,1),0,0)+四((1,四((2,0,1),0,0),1),(四((2,0,1),0,0),1),0,0))",-1],
  ["四(四((M,0,1),0,0))",10],
  ["四(四((四((2,0,1),0,0),0,1),0,0))",10],
  ["四(四((四((M,0,1),0,0),0,1),0,0))",10],
  ["四(四((1,0,0,1),0,0))",5],
  ["四(四((1,0,0,1),0,0)+四((M,1),0,0))",-1],
  ["四(四((1,0,0,1),0,0)+四((四((1,0,0,1),0,0),1),0,0))",-1],
  ["四(四((1,0,0,1),0,0)+四((1,M,1),0,0))",10],
  ["四(四((1,0,0,1),0,0)+四((M,0,1),0,0))",-1],
  ["四(四((1,0,0,1),0,0)+四((四((1,0,0,1),0,0),0,1),0,0))",9],
  ["四(四((1,0,0,1),0,0)+四((四((1,0,0,1),0,0),四((1,0,0,1),0,0),1),0,0))",-1],
  ["四(四((1,0,0,1),(M,1),0,0))",3],
  ["四(四((1,0,0,1),(四((1,0,0,1),0,0),1),0,0))",9],
  ["四(四((1,0,0,1),(1,M,1),0,0))",9],
  ["四(四((1,0,0,1),(1,四((1,0,0,1),0,0),1),0,0))",9],
  ["四(四((1,0,0,1),(M,0,1),0,0))",9],
  ["四(四((1,0,0,1),(四((1,0,0,1),0,0),0,1),0,0))",9],
  ["四(四((1,0,0,M),0,0))",4],
  ["四(四((1,0,0,四((四((1,0,0,1),0,0),0,1),0,0)),0,0))",-1],
  ["四(四((1,0,0,四((1,0,0,1),0,0)),0,0))",6],
  ["四(四((1,0,M,1),0,0))",5],
  ["四(四((1,0,四((四((1,0,0,1),0,0),0,1),0,0),1),0,0))",-1],
  ["四(四((1,0,四((1,0,0,1),0,0),1),0,0))",6],
  ["四(四((1,M,0,1),0,0))",7],
  ["四(四((1,四((四((1,0,0,1),0,0),0,1),0,0),0,1),0,0))",-1],
  ["四(四((1,四((1,0,0,1),0,0),0,1),0,0))",8],
  ["四(四((2,0,0,1),0,0))",-1],
  ["四(四((四((四((1,0,0,1),0,0),0,1),0,0),0,0,1),0,0))",-1],
  ["四(四((四((1,0,0,1),0,0),0,0,1),0,0))",-1],
  ["四(四((1,0,0,0,1),0,0))",-1],
  ["四(四(((ω,1),0,1),0,0))",3],
  ["四(四(((四((M,1),0,0),1),0,1),0,0))",-1],
  ["四(四(((M,1),0,1),0,0))",8],
  ["Ω",5],
  ["四_ω(1)",4],
  ["四((ω,1),ω,1)",5],
  ["四(((ω,1),ω,1),ω,1)",8]
];
/** @type {string[]&{nonstandard:string[]}} */
var testTerms;
function setupTestTerms(){
  document.getElementById('input').value=testTermsPre.filter(function (t){return t[1]>=0;}).map(function(t){return "fund "+t[0]+" "+t[1];}).join("\n");
  testTerms=testTermsPre.map(function (t){return t[0];});
  testTerms.nonstandard=[
    "1+ω",
    "1+Ω",
    "1+四((ω,1),0,0)",
    "四(四_1(四(1,0,0)))",
    "四(四_1(四_2(0)))",
    "四(四(四(1,0,0),0),0)",
    "四(四(四(1,0,0),0),四(1,0,0))",
    "四(四(四(1,0,0),0),四(1,0,0,0))",
    "四(四(四(1,0,0,0),0,0),0,0)",
    "四(四(四(1,0,0,0),0,0),四(1,0,0,0),0)",
    "四(四(四(1,0,0,0),0,0),四(1,0,0,0,0),0)",
    "四(四((M,1),0,0))",
    "四((四((M,1),0,0),1),0,0)",
    "四(M+四((M,1),(四((M,1),0,0),1),0,0))",
    "四(四((1,0,1),0,四((1,0,1),1,0)))",
    "四(四((1,0,1),(四((M,1),0,0),1),0,0))",
    "四((1,0,四((2,0,1),0,0)),(四((M,1),0,0),1),0,0)",
    "四((1,0,四((2,0,1),0,0)),(四((M,1),0,0),1),0,0)",
    "四((1,0,四((2,0,1),0,0)),(四((1,四((2,0,1),0,0),1),0,0),1),0,0)",
    "四((1,四((2,0,1),0,0),1),(四((M,1),0,0),1),0,0)",
    "四((1,四((2,0,1),0,0),1),(四((1,四((2,0,1),0,0),1),0,0),1),0,0)",
    "四((四((四((1,0,0,1),0,0),0,1),0,0),0,1),0,0)",
    "四(四((1,0,0,1),(四((四((1,0,0,1),0,0),0,1),0,0),0,1),0,0))",
  ];
}
/** @param {boolean} logInfoToConsole */
function testFunction(logInfoToConsole){
  var r={lessThan:[],inOT:[],notInOT:[],errors:[]};
  for (var i=0;i<testTerms.length;i++){
    for (var j=0;j<testTerms.length;j++){
      if (logInfoToConsole) console.log("%cTesting: lessThan, "+testTerms[i]+", "+testTerms[j]+".","color:gold");
      var d=Date.now();
      var caught=false;
      var result;
      try{
        result=lessThanT(testTerms[i],testTerms[j]);
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
      result=isStandardT(testTerms[i]);
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
  for (var i=0;i<testTerms.nonstandard.length;i++){
    if (logInfoToConsole) console.log("%cTesting: !inOT, "+testTerms.nonstandard[i]+".","color:gold");
    var d=Date.now();
    var caught=false;
    var result;
    try{
      result=isStandardT(testTerms.nonstandard[i]);
    }catch(e){
      var diff=Date.now()-d;
      r.notInOT.push({arg0:testTerms.nonstandard[i],result:e,time:diff});
      r.errors.push({test:"!inOT",arg0:testTerms.nonstandard[i],name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.notInOT.push({arg0:testTerms.nonstandard[i],result:result,time:diff});
        if (logInfoToConsole) console.log(diff);
        if (result){
          r.errors.push({test:"!inOT",arg0:testTerms.nonstandard[i],name:"fail"});
          console.error("Failed test: !inOT, "+testTerms.nonstandard[i]+".");
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
  "0",
  "1",
  "n",
  "ω",
  "Ω",
  "f[",
  "tf[",
  "M",
  "2四",
  "1四"
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
        }else if (cmd=="inDT"){
          result=inDT(args[0]);
        }else if (cmd=="lessThanOrEqual"||cmd=="<="){
          if (inT(args[0])) result=lessThanOrEqualT(args[0],args[1]);
          else result=lessThanOrEqualDT(args[0],args[1]);
        }else if (cmd=="lessThan"||cmd=="<"){
          if (inT(args[0])){
            if (args.length==2) result=lessThanT(args[0],args[1]);
            else result=bracketLessThanT(args[0],args[1],args[2],args[3]);
          }else{
            if (args.length==2) result=lessThanDT(args[0],args[1]);
            else result=bracketLessThanDT(args[0],args[1],args[2],args[3]);
          }
        }else if (cmd=="bracketLessThan"){
          if (inT(args[0])) result=bracketLessThanT(args[0],args[1],args[2],args[3]);
          else result=bracketLessThanDT(args[0],args[1],args[2],args[3]);
        }else if (cmd=="lessThanOrEqualT"||cmd=="<=T"){
          result=lessThanOrEqualT(args[0],args[1]);
        }else if (cmd=="lessThanT"||cmd=="<T"){
          if (args.length==2) result=lessThanT(args[0],args[1]);
          else result=bracketLessThanT(args[0],args[1],args[2],args[3]);
        }else if (cmd=="bracketLessThanT"){
          result=bracketLessThanT(args[0],args[1],args[2],args[3]);
        }else if (cmd=="lessThanOrEqualDT"||cmd=="<=DT"){
          result=lessThanOrEqualDT(args[0],args[1]);
        }else if (cmd=="lessThanDT"||cmd=="<DT"){
          if (args.length==2) result=lessThanDT(args[0],args[1]);
          else result=bracketLessThanDT(args[0],args[1],args[2],args[3]);
        }else if (cmd=="bracketLessThanDT"){
          result=bracketLessThanDT(args[0],args[1],args[2],args[3]);
        }else if (cmd=="getZero"||cmd=="零位"){
          result=getZero(args[0]);
        }else if (cmd=="setZero"||cmd=="零位変更"){
          result=setZero(args[0],args[1]);
        }else if (cmd=="set"||cmd=="成分変更"){
          result=set(args[0],args[1],args[2]);
        }else if (cmd=="getRightmostNonzero"||cmd=="右端"){
          result=getRightmostNonzero(args[0]);
        }else if (cmd=="setRightmostNonzero"||cmd=="右端成分変更"){
          result=setRightmostNonzero(args[0],args[1]);
        }else if (cmd=="shrinkRightmostNonzero"||cmd=="右端縮小"){
          result=shrinkRightmostNonzero(args[0]);
        }else if (cmd=="maximumElement"||cmd=="出現項上限"){
          result=maximumElement(args[0]);
        }else if (cmd=="maximumEntry"||cmd=="成分上限"){
          result=maximumEntry(args[0]);
        }else if (cmd=="embeddable"||cmd=="埋め込み可能"){
          result=embeddable(args[0],args[1]);
        }else if (cmd=="constructible"||cmd=="構成可能"){
          if (inT(args[0])) result=constructibleT(args[0],args[1]);
          else result=constructibleDT(args[0],args[1]);
        }else if (cmd=="constructibleDT"||cmd=="構成可能DT"){
          result=constructibleDT(args[0],args[1]);
        }else if (cmd=="constructibleT"||cmd=="構成可能T"){
          result=constructibleT(args[0],args[1]);
        }else if (cmd=="entriesSelfConstructible"||cmd=="各引数が自身で構成可能"){
          result=entriesSelfConstructible(args[0]);
        }else if (cmd=="isReduced"||cmd=="簡約"){
          result=isReduced(args[0]);
        }else if (cmd=="isStandard"||cmd=="標準形"){
          if (inT(args[0])) result=isStandardT(args[0]);
          else result=isStandardDT(args[0]);
        }else if (cmd=="isStandardT"||cmd=="標準形T"){
          result=isStandardT(args[0]);
        }else if (cmd=="entriesStandard"||cmd=="各引数が標準形"){
          result=entriesStandard(args[0]);
        }else if (cmd=="isStandardDT"||cmd=="標準形DT"){
          result=isStandardDT(args[0]);
        }else if (cmd=="inOT"){
          result=inOT(args[0]);
        }else if (cmd=="fund"){
          var t=normalizeAbbreviations(args[fundMethods.indexOf(args[0])!=-1?1:0]);
          var method=fundMethods.indexOf(args[0])!=-1?args[0]:undefined;
          result=[t];
          for (var i=fundMethods.indexOf(args[0])!=-1?2:1;i<args.length;i++){
            result.push(t=fund(t,+args[i],method));
          }
        }else{
          result=null;
        }
      }catch(e){
        result=e;
        console.error(e);
      }
      last[l]=result;
      clearMemos();
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
    }else if (cmd=="inDT"){
      output+=result;
    }else if (cmd=="lessThanOrEqual"||cmd=="<="){
      output+=result;
    }else if (cmd=="lessThan"||cmd=="<"){
      output+=result;
    }else if (cmd=="bracketLessThan"){
      output+=result;
    }else if (cmd=="lessThanOrEqualT"||cmd=="<=T"){
      output+=result;
    }else if (cmd=="lessThanT"||cmd=="<T"){
      output+=result;
    }else if (cmd=="bracketLessThanT"){
      output+=result;
    }else if (cmd=="lessThanOrEqualDT"||cmd=="<=DT"){
      output+=result;
    }else if (cmd=="lessThanDT"||cmd=="<DT"){
      output+=result;
    }else if (cmd=="bracketLessThanDT"){
      output+=result;
    }else if (cmd=="getZero"||cmd=="零位"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="setZero"||cmd=="零位変更"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="set"||cmd=="成分変更"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="getRightmostNonzero"||cmd=="右端"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="setRightmostNonzero"||cmd=="右端成分変更"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="shrinkRightmostNonzero"||cmd=="右端縮小"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="maximumElement"||cmd=="出現項上限"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="maximumEntry"||cmd=="成分上限"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="embeddable"||cmd=="埋め込み可能"){
      output+=abbreviateIfEnabled(result);
    }else if (cmd=="constructible"||cmd=="構成可能"){
      output+=result;
    }else if (cmd=="constructibleDT"||cmd=="構成可能DT"){
      output+=result;
    }else if (cmd=="constructibleT"||cmd=="構成可能T"){
      output+=result;
    }else if (cmd=="entriesSelfConstructible"||cmd=="各引数が自身で構成可能"){
      output+=result;
    }else if (cmd=="isReduced"||cmd=="簡約"){
      output+=result;
    }else if (cmd=="isStandard"||cmd=="標準形"){
      output+=result;
    }else if (cmd=="isStandardT"||cmd=="標準形T"){
      output+=result;
    }else if (cmd=="entriesStandard"||cmd=="各引数が標準形"){
      output+=result;
    }else if (cmd=="isStandardDT"||cmd=="標準形DT"){
      output+=result;
    }else if (cmd=="inOT"){
      output+=result;
    }else if (cmd=="fund"){
      if (options.detail){
        for (var i=fundMethods.indexOf(args[0])!=-1?2:1;i<result.length;i++){
          output+=abbreviateIfEnabled(result[i-1])+"["+args[i]+"]="+abbreviateIfEnabled(result[i])+(i==result.length-1?"":"\n");
        }
      }else{
        output+=abbreviateIfEnabled(result[result.length-1]);
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
window.onerror=function (e,s,l,c,o){alert(JSON.stringify(e+"\n"+s+":"+l+":"+c+"\n"+(o&&o.stack)))};