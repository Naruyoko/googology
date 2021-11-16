var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ]/g;
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
    }else if (next=="ψ"||next=="p"||next=="("){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var subterms=[];
      if (next=="ψ"||next=="p"){
        var nextnext=scanner.next();
        if (nextnext!="_"&&nextnext!="(") throw Error("Expected _ or ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        if (nextnext=="_"){
          subterms.push(Term.build(scanner,PSITERMSUBSCRIPT));
          var nextnext=scanner.next();
          if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        }
      }
      while (subterms.length<4){
        subterms.push(Term.build(scanner,PSITERMINNER));
        var nextnext=scanner.next();
        if (nextnext==","){
          if (subterms.length>=4) throw Error("Too many terms in ψ term at position "+scanpos+" in expression "+scanner.s);
        }else if (nextnext==")") break;
        else throw Error("Expected a comma or closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      }
      while (subterms.length<4) subterms.unshift(ZeroTerm.build());
      appendToRSum(PsiTerm.buildNoClone.apply(null,subterms));
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
    if (state==CLOSEDTERM){
      var peek=scanner.peek();
      if (context==BRACES&&peek=="}"){
        state=EXIT;
      }else if (context==PSITERMSUBSCRIPT&&peek=="("){
        state=EXIT;
      }else if (context==PSITERMINNER&&(peek==","||peek==")")){
        state=EXIT;
      }
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
PsiTerm.build=function (sub,inner1,inner2,inner3){
  var r=PsiTerm();
  r.sub=Term(sub);
  r.inner1=Term(inner1);
  r.inner2=Term(inner2);
  r.inner3=Term(inner3);
  return r;
}
PsiTerm.buildNoClone=function (sub,inner1,inner2,inner3){
  var r=PsiTerm();
  r.sub=sub;
  r.inner1=inner1;
  r.inner2=inner2;
  r.inner3=inner3;
  return r;
}
PsiTerm.prototype=Object.create(Term.prototype);
PsiTerm.prototype.clone=function (){
  return PsiTerm.build(this.sub,this.inner1,this.inner2,this.inner3);
}
PsiTerm.prototype.toString=function (abbreviate){
  if (abbreviate&&this.equal(Term.ONE)) return "1";
  else if (abbreviate&&this.equal(Term.SMALLOMEGA)) return "ω";
  else if (abbreviate&&this.sub.equal(Term.ZERO)){
    if (this.inner1.equal(Term.ZERO)){
      if (this.inner2.equal(Term.ZERO)) return "ψ("+this.inner3.toString(abbreviate)+")";
      else return "ψ("+this.inner2.toString(abbreviate)+","+this.inner3.toString(abbreviate)+")";
    }else return "ψ("+this.inner1.toString(abbreviate)+","+this.inner2.toString(abbreviate)+","+this.inner3.toString(abbreviate)+")";
  }else return "ψ_"+this.sub.toStringWithImplicitBrace(abbreviate)+"("+this.inner1.toString(abbreviate)+","+this.inner2.toString(abbreviate)+","+this.inner3.toString(abbreviate)+")";
}
PsiTerm.prototype.equal=function (other){
  if (!(other instanceof Term)) other=Term(other);
  return other instanceof PsiTerm&&this.sub.equal(other.sub)&&this.inner1.equal(other.inner1)&&this.inner2.equal(other.inner2)&&this.inner3.equal(other.inner3);
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
Term.ONE=new Term("ψ_0(0,0,0)");
Term.SMALLOMEGA=new Term("ψ_0(0,0,1)");

function inT(t){
  try{
    t=Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof ZeroTerm) return true;
  if (t instanceof PsiTerm) return inT(t.sub)&&inT(t.inner1)&&inT(t.inner2)&&inT(t.inner3);
  if (t instanceof SumTerm) return t.terms.every(inPT);
  return false;
}
function inPT(t){
  try{
    t=Term(t);
  }catch(e){
    return false;
  }
  if (t instanceof PsiTerm) return inT(t.sub)&&inT(t.inner1)&&inT(t.inner2)&&inT(t.inner3);
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
  return t.equal("1")||isSumAndTermsSatisfy(t,equal("1"));
}
function toNat(X){
  X=Term(X);
  if (!isNat(X)) throw Error("Invalid argument: "+X);
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
function lessThan(X,Y){
  X=Term(X);
  Y=Term(Y);
  if (X instanceof ZeroTerm) return !(Y instanceof ZeroTerm); //1
  if (X instanceof PsiTerm){ //2
    if (Y instanceof ZeroTerm) return false; //2.1
    if (Y instanceof PsiTerm){ //2.2
      if (X.sub.equal(Y.sub)){ //2.2.1
        if (X.inner1.equal(Y.inner1)){
          if (X.inner2.equal(Y.inner2)) return lessThan(X.inner3,Y.inner3); //2.2.1.1
          else return lessThan(X.inner2,Y.inner2); //2.2.1.2
        }else return lessThan(X.inner1,Y.inner1); //2.2.1.3
      }else return lessThan(X.sub,Y.sub); //2.2.2
    }
    if (Y instanceof SumTerm) return equal(X,Y.getLeft())||lessThan(X,Y.getLeft()); //2.3
  }
  if (X instanceof SumTerm){ //3
    if (Y instanceof ZeroTerm) return false; //3.1
    if (Y instanceof PsiTerm) return lessThan(X.getLeft(),Y); //3.2
    if (Y instanceof SumTerm){ //3.3
      if (equal(X.getLeft(),Y.getLeft())) return lessThan(X.getNotLeft(),Y.getNotLeft()); //3.3.1
      else return lessThan(X.getLeft(),Y.getLeft()); //3.3.2
    }
  }
  throw Error("No rule to compare "+X+" and "+Y);
}
function dom(X){
  X=Term(X);
  if (!inT(X)) throw Error("Invalid argument: "+X);
  var temp={};
  function calcTemp(s){
    temp[s]=eval(s);
  }
  if (X instanceof ZeroTerm) return "0"; //1
  if (X instanceof PsiTerm){ //2
    calcTemp("dom(X.inner3)");
    if (equal(temp["dom(X.inner3)"],"0")){ //2.1
      calcTemp("dom(X.inner2)");
      if (equal(temp["dom(X.inner2)"],"0")){ //2.1.1
        calcTemp("dom(X.inner1)");
        if (equal(temp["dom(X.inner1)"],"0")){ //2.1.1.1
          calcTemp("dom(X.sub)");
          if (equal(temp["dom(X.sub)"],"0")||equal(temp["dom(X.sub)"],"1")) return X+""; //2.1.1.1.1
          else return temp["dom(X.sub)"]; //2.1.1.1.2
        }else if (equal(temp["dom(X.inner1)"],"1")) return X+""; //2.1.1.2
        else{ //2.1.1.3
          if (lessThan(temp["dom(X.inner1)"],X)) return temp["dom(X.inner1)"]; //2.1.1.3.1
          else return normalizeAbbreviations("ω"); //2.1.1.3.2
        }
      }else if (equal(temp["dom(X.inner2)"],"1")) return X+""; //2.1.2
      else{ //2.1.3
        if (lessThan(temp["dom(X.inner2)"],X)) return temp["dom(X.inner2)"]; //2.1.3.1
        else return normalizeAbbreviations("ω"); //2.1.3.2
      }
    }else if (equal(temp["dom(X.inner3)"],"1")||equal(temp["dom(X.inner3)"],"ω")) return normalizeAbbreviations("ω"); //2.2
    else{ //2.3
      if (lessThan(temp["dom(X.inner3)"],X)) return temp["dom(X.inner3)"]; //2.3.1
      else return normalizeAbbreviations("ω"); //2.3.2
    }
  }
  if (X instanceof SumTerm) return dom(X.getRight()); //3
  throw Error("No rule to compute dom of "+X);
}
function fund(X,Y){
  X=Term(X);
  if (typeof Y=="number") Y=String(Y);
  Y=Term(Y);
  if (!inT(X)||!inT(Y)) throw Error("Invalid argument: "+X+","+Y);
  var temp={};
  function calcTemp(s){
    temp[s]=eval(s);
  }
  if (X instanceof ZeroTerm) return "0"; //1
  if (X instanceof PsiTerm){ //2
    calcTemp("dom(X.inner3)");
    if (equal(temp["dom(X.inner3)"],"0")){ //2.1
      calcTemp("dom(X.inner2)");
      if (equal(temp["dom(X.inner2)"],"0")){ //2.1.1
        calcTemp("dom(X.inner1)");
        if (equal(temp["dom(X.inner1)"],"0")){ //2.1.1.1
          calcTemp("dom(X.sub)");
          if (equal(temp["dom(X.sub)"],"0")) return "0"; //2.1.1.1.1
          else if (equal(temp["dom(X.sub)"],"1")) return Y+""; //2.1.1.1.2
          else return "ψ_"+fund(X.sub,Y)+"("+X.inner1+","+X.inner2+","+X.inner3+")"; //2.1.1.1.3
        }else if (equal(temp["dom(X.inner1)"],"1")) return Y+""; //2.1.1.2
        else{ //2.1.1.3
          if (lessThan(temp["dom(X.inner1)"],X)) return "ψ_"+X.sub+"("+fund(X.inner1,Y)+","+X.inner2+","+X.inner3+")"; //2.1.1.3.1
          else{ //2.1.1.3.2
            var temp1=Term(temp["dom(X.inner1)"]);
            var P=temp1.sub;
            var Q=temp1.inner1;
            var R=temp1.inner2;
            if (equal(R,"0")){ //2.1.1.3.2.1
              if (equal(Q,"0")){ //2.1.1.3.2.1.1
                if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner2,temp['Term(fund(X,fund(Y,"0")))'].inner2)&&equal(X.inner3,temp['Term(fund(X,fund(Y,"0")))'].inner3))) return "ψ_"+X.sub+"("+fund(X.inner1,"ψ_"+fund(P,"0")+"("+temp['Term(fund(X,fund(Y,"0")))'].inner1+",0,0)")+","+X.inner2+","+X.inner3+")"; //2.1.1.3.2.1.1.1
                else return "ψ_"+X.sub+"("+fund(X.inner1,"ψ_"+fund(P,"0")+"("+Q+","+R+",0)")+","+X.inner2+","+X.inner3+")"; //2.1.1.3.2.1.1.2
              }else{ //2.1.1.3.2.1.2
                if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner2,temp['Term(fund(X,fund(Y,"0")))'].inner2)&&equal(X.inner3,temp['Term(fund(X,fund(Y,"0")))'].inner3))) return "ψ_"+X.sub+"("+fund(X.inner1,"ψ_"+P+"("+fund(Q,"0")+","+temp['Term(fund(X,fund(Y,"0")))'].inner1+",0)")+","+X.inner2+","+X.inner3+")"; //2.1.1.3.2.1.2.1
                else return "ψ_"+X.sub+"("+fund(X.inner1,"ψ_"+P+"("+fund(Q,"0")+","+R+",0)")+","+X.inner2+","+X.inner3+")"; //2.1.1.3.2.1.2.2
              }
            }else{ //2.1.1.3.2.2
              if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner2,temp['Term(fund(X,fund(Y,"0")))'].inner2)&&equal(X.inner3,temp['Term(fund(X,fund(Y,"0")))'].inner3))) return "ψ_"+X.sub+"("+fund(X.inner1,"ψ_"+P+"("+Q+","+fund(R,"0")+","+temp['Term(fund(X,fund(Y,"0")))'].inner1+")")+","+X.inner2+","+X.inner3+")"; //2.1.1.3.2.2.1
              else return "ψ_"+X.sub+"("+fund(X.inner1,"ψ_"+P+"("+Q+","+fund(R,"0")+",0)")+","+X.inner2+","+X.inner3+")"; //2.1.1.3.2.2.2
            }
          }
        }
      }else if (equal(temp["dom(X.inner2)"],"1")) return Y+""; //2.1.2
      else{ //2.1.3
        if (lessThan(temp["dom(X.inner2)"],X)) return "ψ_"+X.sub+"("+X.inner1+","+fund(X.inner2,Y)+","+X.inner3+")"; //2.1.3.1
        else{ //2.1.3.2
          var temp1=Term(temp["dom(X.inner2)"]);
          var P=temp1.sub;
          var Q=temp1.inner1;
          var R=temp1.inner2;
          if (equal(R,"0")){ //2.1.3.2.1
            if (equal(Q,"0")){ //2.1.3.2.1.1
              if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner1,temp['Term(fund(X,fund(Y,"0")))'].inner1)&&equal(X.inner3,temp['Term(fund(X,fund(Y,"0")))'].inner3))) return "ψ_"+X.sub+"("+X.inner1+","+fund(X.inner2,"ψ_"+fund(P,"0")+"("+temp['Term(fund(X,fund(Y,"0")))'].inner2+",0,0)")+","+X.inner3+")"; //2.1.3.2.1.1.1
              else return "ψ_"+X.sub+"("+X.inner1+","+fund(X.inner2,"ψ_"+fund(P,"0")+"("+Q+","+R+",0)")+","+X.inner3+")"; //2.1.3.2.1.1.2
            }else{ //2.1.3.2.1.2
              if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner1,temp['Term(fund(X,fund(Y,"0")))'].inner1)&&equal(X.inner3,temp['Term(fund(X,fund(Y,"0")))'].inner3))) return "ψ_"+X.sub+"("+X.inner1+","+fund(X.inner2,"ψ_"+P+"("+fund(Q,"0")+","+temp['Term(fund(X,fund(Y,"0")))'].inner2+",0)")+","+X.inner3+")"; //2.1.3.2.1.2.1
              else return "ψ_"+X.sub+"("+X.inner1+","+fund(X.inner2,"ψ_"+P+"("+fund(Q,"0")+","+R+",0)")+","+X.inner3+")"; //2.1.3.2.1.2.2
            }
          }else{ //2.1.3.2.2
            if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner1,temp['Term(fund(X,fund(Y,"0")))'].inner1)&&equal(X.inner3,temp['Term(fund(X,fund(Y,"0")))'].inner3))) return "ψ_"+X.sub+"("+X.inner1+","+fund(X.inner2,"ψ_"+P+"("+Q+","+fund(R,"0")+","+temp['Term(fund(X,fund(Y,"0")))'].inner3+")")+","+X.inner3+")"; //2.1.3.2.2.1
            else return "ψ_"+X.sub+"("+X.inner1+","+fund(X.inner2,"ψ_"+P+"("+Q+","+fund(R,"0")+",0)")+","+X.inner3+")"; //2.1.3.2.2.2
          }
        }
      }
    }else if (equal(temp["dom(X.inner3)"],"1")){ //2.2
      if (equal(Y,"1")) return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,"0")+")"; //2.2.1
      else if (isNat(Y)) return Array(toNat(Y)).fill("ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,"0")+")").join("+"); //2.2.2
      else return "0"; //2.2.3
    }else if (equal(temp["dom(X.inner3)"],"ω")) return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,Y)+")"; //2.3
    else{ //2.4
      if (lessThan(temp["dom(X.inner3)"],X)) return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,Y)+")"; //2.4.1
      else{ //2.4.2
        var temp1=Term(temp["dom(X.inner3)"]);
        var P=temp1.sub;
        var Q=temp1.inner1;
        var R=temp1.inner2;
        if (equal(R,"0")){ //2.4.2.1
          if (equal(Q,"0")){ //2.4.2.1.1
            if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner1,temp['Term(fund(X,fund(Y,"0")))'].inner1)&&equal(X.inner2,temp['Term(fund(X,fund(Y,"0")))'].inner2))) return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,"ψ_"+fund(P,"0")+"("+temp['Term(fund(X,fund(Y,"0")))'].inner3+",0,0)")+")"; //2.4.2.1.1.1
            else return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,"ψ_"+fund(P,"0")+"("+Q+","+R+","+Y+")")+")"; //2.4.2.1.1.2
          }else{ //2.4.2.1.2
            if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner1,temp['Term(fund(X,fund(Y,"0")))'].inner1)&&equal(X.inner2,temp['Term(fund(X,fund(Y,"0")))'].inner2))) return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,"ψ_"+P+"("+fund(Q,"0")+","+temp['Term(fund(X,fund(Y,"0")))'].inner3+",0)")+")"; //2.4.2.1.2.1
            else return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,"ψ_"+P+"("+fund(Q,"0")+","+R+",0)")+")"; //2.4.2.1.2.2
          }
        }else{ //2.4.2.2
          if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(X.sub,temp['Term(fund(X,fund(Y,"0")))'].sub)&&equal(X.inner1,temp['Term(fund(X,fund(Y,"0")))'].inner1)&&equal(X.inner2,temp['Term(fund(X,fund(Y,"0")))'].inner2))) return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,"ψ_"+P+"("+Q+","+fund(R,"0")+","+temp['Term(fund(X,fund(Y,"0")))'].inner3+")")+")"; //2.4.2.2.1
          else return "ψ_"+X.sub+"("+X.inner1+","+X.inner2+","+fund(X.inner3,"ψ_"+P+"("+Q+","+fund(R,"0")+",0)")+")"; //2.4.2.2.2
        }
      }
    }
  }
  if (X instanceof SumTerm){ //3
    calcTemp("fund(X.getRight(),Y)");
    if (equal(temp["fund(X.getRight(),Y)"],"0")) return X.getNotRight()+""; //3.1;3.2
    else return X.getNotRight()+"+"+temp["fund(X.getRight(),Y)"]; //3.3
  }
  throw Error("No rule to compute fund of "+X+","+Y);
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
    while(n<=limit&&!(equal(x,t=limitOrd(n))||lessThan(x,t))){
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
function isStandard(x,limit){
  return findOTPath(x,limit).isStandard;
}
//ψ_0(Λ(n))
function limitOrd(n){
  return "ψ_0(0,0,"+"ψ_".repeat(n+1)+"0"+"(0,0,0)".repeat(n+1)+")";
}
function FGH(X,n){
  X=normalizeAbbreviations(X);
  if (!isStandard(X)||(typeof n!="number")) throw Error("Invalid argument: "+X);
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
  var ord=limitOrd(n);
  var r=n;
  for (var i=0;i<n;i++) r=FGH(ord,r);
  return r;
}
function calculateN(){
  return largeFunction(1e100);
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
  function abbreviateIfEnabled(x){
    if (options.abbreviate) return abbreviate(x);
    else return x;
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
        }else if (cmd=="lessThan"||cmd=="<"){
          result=lessThan(args[0],args[1]);
        }else if (cmd=="dom"){
          result=dom(args[0]);
        }else if (cmd=="expand"){
          var t=normalizeAbbreviations(args[0]);
          result=[t];
          for (var i=1;i<args.length;i++){
            result.push(t=fund(t,args[i]));
          }
        }else if (cmd=="isStandard"){
          result=findOTPath(args[0],args[1]||3);
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
      output+=result;
    }else if (cmd=="lessThan"||cmd=="<"){
      output+=result;
    }else if (cmd=="dom"){
      output+=abbreviateIfEnabled(result);
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
        else output+=abbreviateIfEnabled(args[0])+"∉OT limited to n≦"+(args[1]||3);
      }else{
        output+=result.isStandard;
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