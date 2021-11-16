var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ,]/g;
window.onload=function (){
  console.clear();
  dg('input').onkeydown=handlekey;
  dg('input').onfocus=handlekey;
  dg('input').onmousedown=handlekey;
}
function dg(s){
  return document.getElementById(s);
}

function normalizeAbbreviations(s){
  return Term(s+"")+"";
}
function abbreviate(s){
  return Term(s+"").toString(true);
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

function Term(s){
  if (s instanceof Term) return s.clone();
  else if (typeof s!="undefined"&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (s) return Term.build(s);
  else return this;
}
Term.build=function (s,context){
  if (s instanceof Term) return s.clone();
  function appendToRSum(term){
    if (state==START) r=term;
    else if (state==PLUS) r=SumTerm.buildNoClone([r,term]);
    else throw Error("Wrong state when attempting to append as sum");
    state=CLOSEDTERM;
  }
  var nums="0123456789";
  var scanner;
  if (typeof s=="string") scanner=new Scanner(s);
  else if (s instanceof Scanner) scanner=s;
  else throw Error("Invalid expression: "+s);
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
    }else if (next=="ω"||next=="w"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(Term.SMALLOMEGA.clone());
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
        appendToRSum(PsiTerm.buildNoClone(ZeroTerm.build(),innerterm));
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
        r=SubTerm.buildNoClone([r,subterm]);
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
    else if (state==CLOSEDTERM);
  }else{
    if (!scanner.hasNext()) throw Error("Unexpected end of input");
    if (state==START) r=ZeroTerm.build();
    else if (state==PLUS) throw Error("Something went wrong");
    else if (state==CLOSEDTERM);
  }
  return r;
}
Term.buildNoClone=function (){
  throw Error("Not implemented");
}
Term.prototype.clone=function (){
  throw Error("Cloning undefined for this term type.");
}
Term.clone=function (x){
  return x.clone();
}
Term.prototype.toString=function (abbreviate){
  throw Error("Stringification undefined for this term type.");
}
Term.prototype.toStringWithImplicitBrace=function (abbreviate){
  return this.toString(abbreviate);
}
Term.prototype.equal=function (other){
  throw Error("Equality undefined for this term type.");
}
Term.equal=function (x,y){
  if (!(x instanceof Term)) x=Term(x);
  x.equal(y);
}
Object.defineProperty(Term.prototype,"constructor",{
  value:Term,
  enumerable:false,
  writable:true
});

function NullTerm(s){
  if (s instanceof NullTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof NullTerm)) return new NullTerm(s);
  var r=Term.call(this,s);
  if (s&&!(r instanceof NullTerm)) throw Error("Invalid expression: "+s);
  if (s) return r;
}
Object.assign(NullTerm,Term);
NullTerm.build=function (){
  var r=NullTerm();
  return r;
}
NullTerm.buildNoClone=function (){
  var r=NullTerm();
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
  if (!(other instanceof Term)) other=Term(other);
  return other instanceof NullTerm;
}
Object.defineProperty(NullTerm.prototype,"constructor",{
  value:NullTerm,
  enumerable:false,
  writable:true
});

function ZeroTerm(s){
  if (s instanceof ZeroTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof ZeroTerm)) return new ZeroTerm(s);
  var r=Term.call(this,s);
  if (s&&!(r instanceof ZeroTerm)) throw Error("Invalid expression: "+s);
  if (s) return r;
}
Object.assign(ZeroTerm,Term);
ZeroTerm.build=function (){
  var r=ZeroTerm();
  return r;
}
ZeroTerm.buildNoClone=function (){
  var r=ZeroTerm();
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
  if (!(other instanceof Term)) other=Term(other);
  return other instanceof ZeroTerm;
}
Object.defineProperty(ZeroTerm.prototype,"constructor",{
  value:ZeroTerm,
  enumerable:false,
  writable:true
});

function PsiTerm(s){
  if (s instanceof PsiTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof PsiTerm)) return new PsiTerm(s);
  var r=Term.call(this,s);
  if (s&&!(r instanceof PsiTerm)) throw Error("Invalid expression: "+s);
  if (s) return r;
}
Object.assign(PsiTerm,Term);
PsiTerm.build=function (sub,inner){
  var r=PsiTerm();
  r.sub=Term(sub);
  r.inner=Term(inner);
  return r;
}
PsiTerm.buildNoClone=function (sub,inner){
  var r=PsiTerm();
  r.sub=sub;
  r.inner=inner;
  return r;
}
PsiTerm.prototype=Object.create(Term.prototype);
PsiTerm.prototype.clone=function (){
  return PsiTerm.build(this.sub,this.inner);
}
PsiTerm.prototype.toString=function (abbreviate){
  if (abbreviate&&this.equal(Term.ONE)) return "1";
  else if (abbreviate&&this.equal(Term.SMALLOMEGA)) return "ω";
  else if (abbreviate&&this.sub.equal(Term.ZERO)) return "ψ("+this.inner.toString(abbreviate)+")";
  else return "ψ_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner.toString(abbreviate)+")";
}
PsiTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=Term(other);
  return other instanceof PsiTerm&&this.sub.equal(other.sub)&&this.inner.equal(other.inner);
}
Object.defineProperty(PsiTerm.prototype,"constructor",{
  value:PsiTerm,
  enumerable:false,
  writable:true
});

function SumTerm(s){
  if (s instanceof SumTerm) return s.clone();
  else if (s instanceof Term&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (!(this instanceof SumTerm)) return new SumTerm(s);
  var r=Term.call(this,s);
  if (s&&!(r instanceof SumTerm)) throw Error("Invalid expression: "+s);
  if (s) return r;
}
Object.assign(SumTerm,Term);
SumTerm.build=function (terms){
  var r=SumTerm();
  r.terms=[];
  for (var i=0;i<terms.length;i++){
    if (terms[i] instanceof SumTerm){
      r.terms=r.terms.concat(Term(terms[i]).terms);
    }else{
      r.terms.push(Term(terms[i]));
    }
  }
  return r;
}
SumTerm.buildNoClone=function (terms){
  var r=SumTerm();
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
SumTerm.prototype.toString=function (abbreviate){
  if (abbreviate){
    var strterms=this.terms.map(function (t){return t.toString(abbreviate);});
    for (var i=0;i<strterms.length;i++){
      if (strterms[i]=="1"){
        for (var j=i;j<strterms.length&&strterms[j]=="1";j++);
        strterms.splice(i,j-i,(j-i)+"");
      }
    }
    return strterms.join("+");
  }else{
    return this.terms.join("+");
  }
}
SumTerm.prototype.toStringWithImplicitBrace=function (abbreviate){
  if (abbreviate&&isNat(this)) return this.toString(abbreviate);
  else return "{"+this.toString(abbreviate)+"}";
}
SumTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=Term(other);
  return other instanceof SumTerm
    ?this.terms.length==other.terms.length&&this.terms.every(function (e,i){return e.equal(other.terms[i]);})
    :this.terms.length==1&&this.terms[0].equal(other);
}
SumTerm.prototype.getLeft=function (){
  return Term(this.terms[0]);
}
SumTerm.prototype.getNotLeft=function (){
  if (this.terms.length<2) return ZeroTerm.build();
  else if (this.terms.length<=2) return Term(this.terms[1]);
  else return SumTerm.build(this.terms.slice(1));
}
SumTerm.prototype.getRight=function (){
  return Term(this.terms[this.terms.length-1]);
}
SumTerm.prototype.getNotRight=function (){
  if (this.terms.length<2) return ZeroTerm.build();
  else if (this.terms.length<=2) return Term(this.terms[0]);
  else return SumTerm.build(this.terms.slice(0,-1));
}
SumTerm.prototype.slice=function (start,end){
  if (start<0) start=this.terms.length+start;
  if (end===undefined) end=this.terms.length;
  if (end<0) end=this.terms.length+end;
  if (start>=end) return NullTerm.build();
  else if (end-start==1) return Term(this.terms[start]);
  else return SumTerm.build(this.terms.slice(start,end));
}
Object.defineProperty(SumTerm.prototype,"constructor",{
  value:SumTerm,
  enumerable:false,
  writable:true
});

Term.ZERO=new Term("0");
Term.ONE=new Term("ψ_0(0)");
Term.SMALLOMEGA=new Term("ψ_0(1)");

function inT(t){
  try{
    t=Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return true;
  if (t instanceof PsiTerm) return inT(t.sub)&&inT(t.inner);
  if (t instanceof SumTerm) return t.terms.every(inPT);
  return false;
}
function inPT(t){
  try{
    t=Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof PsiTerm) return inT(t.sub)&&inT(t.inner);
  return false;
}
function inRT(t){
  try{
    t=Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return true;
  if (t instanceof PsiTerm) return isNat(t.sub)&&inT(t.sub)&&inT(t.inner);
  if (t instanceof SumTerm) return t.terms.every(inPT);
  return false;
}
function inRPT(t){
  try{
    t=Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof PsiTerm) return isNat(t.sub)&&inT(t.sub)&&inT(t.inner);
  return false;
}
function isSumAndTermsSatisfy(t,f){
  return t instanceof SumTerm&&t.terms.every(f);
}
function isNat(t){
  try{
    t=Term(t);
  }catch(e){
    return false;
  }
  return t.equal("0")||t.equal("1")||isSumAndTermsSatisfy(t,equal("1"));
}
function toNat(X){
  X=Term(X);
  if (!isNat(X)) throw Error("Invalid argument: "+X);
  if (X instanceof ZeroTerm) return 0;
  if (X instanceof PsiTerm) return 1;
  if (X instanceof SumTerm) return X.terms.length;
  throw Error("This should be unreachable");
}
function equal(X,Y){
  if (arguments.length==1) return function(t){return equal(t,X);};
  X=Term(X);
  Y=Term(Y);
  return X.equal(Y);
}
function notEqual(X,Y){
  if (arguments.length==1) return function(t){return notEqual(t,X);};
  return !equal(X,Y);
}
function ascend(S,del,br,pr){
  S=Term(S);
  if (!inRT(S)||typeof del!="number"||del===0||typeof br!="number"||(pr!==0&&pr!==1)) throw Error("Invalid argument: "+S+","+del+","+br+","+pr);
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm) return S.terms.map(function (t){return ascend(t,del,br,pr);}).join("+"); //2
  if (S instanceof PsiTerm&&inRT(S)){ //3
    var a=toNat(S.sub);
    var b=S.inner;
    if (br<a) return "ψ_{"+normalizeAbbreviations(a+del)+"}("+ascend(b,del,br,pr)+")"; //3.1
    else{ //3.2
      if (pr==0) return "ψ_{"+normalizeAbbreviations(a+del)+"}("+ascend(b,del,br,1)+")"; //3.2.1
      else return S+"";
    }
  }
  throw Error("No rule to compute delta("+S+","+del+","+br+","+pr+")");
}
function cp(S){
  S=Term(S);
  if (!inRT(S)) throw Error("Invalid argument: "+S);
  var cache=new Map();
  function cachedCalc(s){
    if (cache.has(s)) return cache.get(s);
    else{
      var r=eval(s);
      cache.set(s,r);
      return r;
    }
  }
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm) return cp(S.getRight()); //2
  if (S instanceof PsiTerm){ //3
    var a=toNat(S.sub);
    var b=S.inner;
    if (equal(cachedCalc("cp(b)"),"0")) return S+""; //3.1
    else if (equal(cachedCalc("cp(b)"),"1")||equal(cachedCalc("cp(b)"),"ω")) return normalizeAbbreviations("ω"); //3.2
    else{ //3.3
      var c=toNat(cachedCalc("Term(cachedCalc('dom(b)'))").sub);
      var d=cachedCalc("Term(cachedCalc('dom(b)'))").inner;
      if (equal(d,"0")){ //3.3.1
        if (a<c) return S+""; //3.3.1.1
        else return cp(b); //3.3.1.2
      }else return cp(b); //3.3.2
    }
  }
  throw Error("No rule to compute cp("+S+")");
}
function dom(S){
  S=Term(S);
  if (!inRT(S)) throw Error("Invalid argument: "+S);
  var cache=new Map();
  function cachedCalc(s){
    if (cache.has(s)) return cache.get(s);
    else{
      var r=eval(s);
      cache.set(s,r);
      return r;
    }
  }
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm) return dom(S.getRight()); //2
  if (S instanceof PsiTerm){ //3
    var a=toNat(S.sub);
    var b=S.inner;
    if (equal(cachedCalc("dom(b)"),"0")) return S+"" //3.1
    else if (equal(cachedCalc("dom(b)"),"1")||equal(cachedCalc("dom(b)"),"ω")) return normalizeAbbreviations("ω"); //3.2
    else{ //3.3
      var c=toNat(cachedCalc("Term(cachedCalc('dom(b)'))").sub);
      var d=cachedCalc("Term(cachedCalc('dom(b)'))").inner;
      if (a<c){ //3.3.1
        var del0=c-a-1;
        if (equal(cachedCalc("dom(d)"),"0")){ //3.3.1.1
          if (del0<1) return normalizeAbbreviations("ω"); //3.3.1.1.1
          else return S+""; //3.3.1.1.2
        }else{ //3.3.1.2
          var e=toNat(cachedCalc("Term(cp(b))").sub);
          var f=cachedCalc("Term(cp(b))").inner;
          var g=toNat(Term(cp(f)).sub);
          var del1=g-e-1;
          if (del0<del1) return normalizeAbbreviations("ω"); //3.3.1.2.1
          else return S+""; //3.3.1.2.2
        }
      }else return cachedCalc("dom(b)"); //3.3.2
    }
  }
  throw Error("No rule to compute dom of "+S);
}
function fund(S,T){
  S=Term(S);
  if (typeof T=="number") T=String(T);
  T=Term(T);
  if (!inRT(S)||!inRT(T)) throw Error("Invalid argument: "+S+","+T);
  var cache=new Map();
  function cachedCalc(s){
    if (cache.has(s)) return cache.get(s);
    else{
      var r=eval(s);
      cache.set(s,r);
      return r;
    }
  }
  if (S instanceof ZeroTerm) return "0"; //1
  if (S instanceof SumTerm){ //2
    var bp=fund(S.getRight(),T);
    if (equal(bp,"0")) return S.getNotRight()+""; //2.1
    else return S.getNotRight()+"+"+bp; //2.2
  }
  if (S instanceof PsiTerm){ //3
    var a=toNat(S.sub);
    var b=S.inner;
    if (equal(cachedCalc("dom(b)"),"0")) return T+""; //3.1
    else if (equal(cachedCalc("dom(b)"),"1")){ //3.2
      if (equal(T.getRight(),"1")) return fund(S,fund(T,"0"))+"+"+fund(S,"1"); //3.2.1
      else return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,"0")+")"; //3.2.2
    }else if (equal(cachedCalc("dom(b)"),"ω")) return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,T)+")"; //3.3
    else{ //3.4
      var c=toNat(cachedCalc("Term(cachedCalc('dom(b)'))").sub);
      var d=cachedCalc("Term(cachedCalc('dom(b)'))").inner;
      if (a<c){ //3.4.1
        var del0=c-a-1;
        if (equal(cachedCalc("dom(d)"),"0")){ //3.4.1.1
          if (del0<1){ //3.4.1.1.1
            if (isNat(T)&&notEqual(T,"0")) return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,fund(S,fund(T,"0")))+")"; //3.4.1.1.1.1
            else return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,"0")+")"; //3.4.1.1.1.2
          }else{ //3.4.1.1.2
            if (T instanceof ZeroTerm) return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,"0")+")"; //3.4.1.1.2.1
            else if (isNat(T)) return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,ascend(fund(S,fund(T,"0")),del0,a,0))+")"; //3.4.1.1.2.2
            else return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,T)+")"; //3.4.1.1.2.3
          }
        }else{ //3.4.1.2
          var e=toNat(cachedCalc("Term(cp(b))").sub);
          var f=cachedCalc("Term(cp(b))").inner;
          var g=toNat(Term(cp(f)).sub);
          var del1=g-e-1;
          var del2=g-a-1;
          if (del0<del1){ //3.4.1.2.1
            if (isNat(T)&&notEqual(T,"0")) return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,ascend(fund(S,fund(T,"0")),del2,a,0))+")"; //3.4.1.2.1.1
            else return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,"0")+")"; //3.4.1.2.1.2
          }else{ //3.4.1.2.2
            if (T instanceof ZeroTerm) return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,"0")+")"; //3.4.1.2.2.1
            else if (isNat(T)) return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,ascend(fund(S,fund(T,"0")),del2,a,0))+")"; //3.4.1.2.2.2
            else return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,T)+")"; //3.4.1.2.2.3
          }
        }
      }else return "ψ_{"+normalizeAbbreviations(a)+"}("+fund(b,T)+")"; //3.4.2
    }
  }
  throw Error("No rule to compute fund of "+S+","+T);
}
function findOTPath(x,limit){
  x=normalizeAbbreviations(x);
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
//ψ_0(ψ_n(0))
function limitOrd(n){
  return "ψ_0(ψ_{"+normalizeAbbreviations(n)+"}(0))";
}
function FGH(X,n){
  X=normalizeAbbreviations(X);
  if (typeof n!="number") throw Error("Invalid argument: "+X);
  if (equal(X,"0")) return n+1;
  else if (equal(dom(X),"1")){
    var r=n;
    var X0=fund(X,"0");
    for (var i=0;i<n;i++) r=FGH(X0,r);
    return r;
  }else return FGH(fund(X,n),n);
}
function largeFunction(n){
  if (typeof n!="number") throw Error("Invalid argument");
  return FGH(limitOrd(n),n);
}
function calculateN(){
  var r=1e100;
  for (var i=0;i<1e100;i++) r=largeFunction(r);
  return r;
}

var input="";
var options={
  abbreviate:undefined,
  detail:undefined
}
var last=null;
function compute(){
  if (input==dg("input").value&&options.abbreviate==dg("abbreviate").checked&&options.detail==dg("detail").checked) return;
  var oldinput=input;
  input=dg("input").value;
  options.abbreviate=dg("abbreviate").checked;
  options.detail=dg("detail").checked;
  if (oldinput!=input) last=[];
  var output="";
  var lines=input.split(lineBreakRegex);
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
        }else if (cmd=="expand"){
          var t=normalizeAbbreviations(args[0]);
          result=[t];
          for (var i=1;i<args.length;i++){
            result.push(t=fund(t,args[i]));
          }
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
    }else if (cmd=="expand"){
      if (options.detail){
        for (var i=1;i<result.length;i++){
          output+=(options.abbreviate?abbreviate(result[i-1]):result[i-1])+"["+args[i]+"]="+(options.abbreviate?abbreviate(result[i]):result[i])+(i==result.length-1?"":"\n");
        }
      }else{
        output+=(options.abbreviate?abbreviate(result[result.length-1]):result[result.length-1]);
      }
    }else{
      output+="Unknown command "+cmd;
    }
    output+="\n\n";
  }
  dg("output").value=output;
}
window.onpopstate=function (e){
  compute();
}
var handlekey=function(e){}
//console.log=function (s){alert(s)};
window.onerror=function (e,s,l,c,o){alert(JSON.stringify(e+"\n"+s+":"+l+":"+c+"\n"+(o&&o.stack)))};