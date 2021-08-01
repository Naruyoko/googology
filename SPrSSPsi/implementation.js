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

function occurrences(string, subString, allowOverlapping) {
  string+="";
  subString+="";
  if (subString.length<=0)return string.length+1;
  var n=0,
  pos=0,
  step=allowOverlapping?1:subString.length;
  while (true){
    pos=string.indexOf(subString,pos);
    if (pos>=0){
      ++n;
      pos+=step;
    }else break;
  }
  return n;
}
function isMatchingParens(s){
  return occurrences(s,"{")==occurrences(s,"}")
    &&occurrences(s,"[")==occurrences(s,"]")
    &&occurrences(s,"(")==occurrences(s,")");
}
function normalizeAbbreviations(s){
  return Term(s)+"";
}
function abbreviate(s){
  return Term(s).toString(true);
}

function Term(s){
  if (s instanceof Term) return s.clone();
  else if (typeof s!="undefined"&&typeof s!="string") throw Error("Invalid expression: "+s);
  if (s) return Term.build(s);
  else return this;
}
Term.build=function (s){
  if (s instanceof Term) return s.clone();
  if (!isMatchingParens(s)) throw Error("Invalid expression: "+s);
  var strin=s;
  if (s=="") return NullTerm.build();
  if (s=="0") return ZeroTerm.build();
  s=s.replaceAll("p","ψ").replaceAll("w","ω");
  if (!/^[ψ_ω0-9\(\){}\+]+$/.test(s)) throw Error("Invalid expression: "+strin);
  var nums="0123456789";
  var alphas="abcdefghij";
  function numToAlpha(n){
    n=n+"";
    for (var i=0;i<10;i++){
      n=n.replaceAll(nums[i],alphas[i]);
    }
    return "<"+n+">";
  }
  function alphaToNum(s){
    if (s[0]!="<"||s[s.length-1]!=">") throw Error("F");
    s=s.slice(1,-1);
    for (var i=0;i<10;i++){
      s=s.replaceAll(alphas[i],nums[i]);
    }
    return +s;
  }
  var subterms=[];
  function newSubterm(t){
    subterms.push(t);
    return numToAlpha(subterms.length-1);
  }
  function getSubterm(n){
    return subterms[alphaToNum(n)];
  }
  s=s.replace(/[0-9]+/g,function (n){return +n<2?n:"{1"+"+1".repeat(+n-1)+"}";});
  while (true){
    var manipulated=false;
    if (s.indexOf("ω")!=-1){ //ω
      manipulated=true;
      s=s.replaceAll("ω",newSubterm(Term("ψ_0(1)")));
    }
    if (s.indexOf("0")!=-1){ //0
      manipulated=true;
      s=s.replaceAll("0",newSubterm(ZeroTerm.build()));
    }
    if (s.indexOf("1")!=-1){ //1
      manipulated=true;
      s=s.replaceAll("1",newSubterm(Term("ψ_0(0)")));
    }
    while (/{<[a-j]+>}/.test(s)){ //{#}->#
      manipulated=true;
      s=s.replace(/{<[a-j]+>}/g,function (s){return s.slice(1,-1);});
    }
    if (/ψ\(<[a-j]+>\)/.test(s)){ //ψ(#)->ψ_0(#)
      manipulated=true;
      s=s.replace(/ψ\(<[a-j]+>\)/g,function (s){return "ψ_0"+s.slice(1);});
    }
    if (/ψ_<[a-j]+>\(<[a-j]+>\)/.test(s)){ //ψ_#(#)->#
      manipulated=true;
      s=s.replace(/ψ_<[a-j]+>\(<[a-j]+>\)/g,function (s){return newSubterm(PsiTerm.build(getSubterm(s.slice(2,s.indexOf("("))),getSubterm(s.slice(s.indexOf("(")+1,-1))));});
    }
    if (/(?<!\+)<[a-j]+>(\+<[a-j]+>)+(?!\+)/.test(s)){ //#+#+...+#->#
      manipulated=true;
      s=s.replace(/(?<!\+)<[a-j]+>(\+<[a-j]+>)+(?!\+)/g,function (s){return newSubterm(SumTerm.build(s.split("+").map(getSubterm)));});
    }
    if (/^<[a-j]+>$/.test(s)) break;
    if (!manipulated) throw Error("Error parsing expression: "+strin);
  }
  return getSubterm(s);
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
PsiTerm.prototype=Object.create(Term.prototype);
PsiTerm.prototype.clone=function (){
  return PsiTerm.build(this.sub,this.inner);
}
PsiTerm.prototype.toString=function (abbreviate){
  if (abbreviate&&this.equal("1")) return "1";
  else if (abbreviate&&this.equal("ω")) return "ω";
  else if (abbreviate&&this.sub.equal("0")) return "ψ("+this.inner.toString(abbreviate)+")";
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
  return other instanceof SumTerm&&this.terms.length==other.terms.length&&this.terms.every(function (e,i){return Term(e).equal(other.terms[i]);});
}
SumTerm.prototype.getLeft=function (){
  return Term(this.terms[0]);
}
SumTerm.prototype.getNotLeft=function (){
  if (this.terms.length<=2) return Term(this.terms[1]);
  else return SumTerm.build(this.terms.slice(1));
}
SumTerm.prototype.getRight=function (){
  return Term(this.terms[this.terms.length-1]);
}
SumTerm.prototype.getNotRight=function (){
  if (this.terms.length<=2) return Term(this.terms[0]);
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
  if (Y instanceof ZeroTerm) return false; //1
  if (X instanceof ZeroTerm) return true; //2
  if (X instanceof SumTerm){ //3
    if (Y instanceof SumTerm) //3.1
      return lessThan(X.getLeft(),Y.getLeft()) //3.1.1
        ||equal(X.getLeft(),Y.getLeft())&&lessThan(X.getNotLeft(),Y.getNotLeft()); //3.1.2
    if (Y instanceof PsiTerm) return lessThan(X.getLeft(),Y); //3.2
  }
  if (X instanceof PsiTerm){ //4
    if (Y instanceof SumTerm) return lessThanOrEqual(X,Y.getLeft()) //4.1
    if (Y instanceof PsiTerm) //4.2
      return lessThan(X.sub,Y.sub) //4.2.1
        ||equal(X.sub,Y.sub)&&lessThan(X.inner,Y.inner); //4.2.2
  }
  throw Error("No rule to compare "+X+" and "+Y);
}
function lessThanOrEqual(X,Y){
  X=Term(X);
  Y=Term(Y);
  return equal(X,Y)||lessThan(X,Y);
}
function code(X){
  X=Term(X);
  if (!inT(X)) throw Error("Invalid argument: "+X);
  if (X instanceof ZeroTerm) return 0;
  if (X instanceof PsiTerm) return equal(X,"1")?1:0;
  if (X instanceof SumTerm){
    var r=0;
    var i=X.terms.length-1;
    while (i>=0&&equal(X.terms[i],"1")){
      r++;
      i--;
    }
    return r;
  }
}
function ascend(X,Y,Z){
  X=Term(X);
  if (!inT(X)||typeof Y!="number"||Y===0||typeof Z!="number") throw Error("Invalid argument: "+X+","+Y+","+Z);
  if (X instanceof ZeroTerm) return "0"; //1
  if (X instanceof SumTerm) return X.terms.map(function (t){return ascend(t,Y,Z);}).join("+"); //2
  if (X instanceof PsiTerm){ //3
    if (Z<code(X.sub)) return "ψ_{"+X.sub+"+"+Y+"}("+ascend(X.inner,Y,Z)+")"; //3.1
    else return X+""; //3.2
  }
  throw Error("No rule to compute delta("+X+","+Y+","+Z+")");
}
function dom(X){
  X=Term(X);
  if (!inT(X)) throw Error("Invalid argument: "+X);
  var temp={};
  function calcTemp(s){
    temp[s]=eval(s);
  }
  if (X instanceof ZeroTerm) return "0"; //1
  if (X instanceof SumTerm) return dom(X.getRight()); //2
  if (X instanceof PsiTerm){ //3
    calcTemp("dom(X.inner)");
    if (equal(temp["dom(X.inner)"],"0")){ //3.1
      calcTemp("dom(X.sub)");
      if (equal(temp["dom(X.sub)"],"0")||equal(temp["dom(X.sub)"],"1")) return X+""; //3.1.1
      else return temp["dom(X.sub)"]; //3.1.2
    }else if (equal(temp["dom(X.inner)"],"1")||equal(temp["dom(X.inner)"],"ω")) return normalizeAbbreviations("ω"); //3.2
    else{ //3.3
      if (lessThan(temp["dom(X.inner)"],X)) return temp["dom(X.inner)"]; //3.3.1
      else return normalizeAbbreviations("ω"); //3.3.2
    }
  }
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
  if (X instanceof SumTerm){ //2
    var bp=fund(X.getRight(),Y);
    if (equal(bp,"0")) return X.getNotRight()+""; //2.1
    else return X.getNotRight()+"+"+bp; //2.2
  }
  if (X instanceof PsiTerm){ //3
    calcTemp("dom(X.inner)");
    if (equal(temp["dom(X.inner)"],"0")){ //3.1
      calcTemp("dom(X.sub)");
      if (equal(temp["dom(X.sub)"],"0")||equal(temp["dom(X.sub)"],"1")) return Y+""; //3.1.1
      else return "ψ_"+fund(X.sub,Y)+"("+X.inner+")"; //3.1.2
    }else if (equal(temp["dom(X.inner)"],"1")){ //3.2
      calcTemp('fund(Y,"0")');
      if (equal(Y,temp['fund(Y,"0")']+"+1")) return fund(X,temp['fund(Y,"0")'])+"+"+fund(X,"1"); //3.2.1
      else return "ψ_"+X.sub+"("+fund(X.inner,"0")+")"; //3.2.2
    }else if (equal(temp["dom(X.inner)"],"ω")) return "ψ_"+X.sub+"("+fund(X.inner,Y)+")"; //3.3
    else{ //3.4
      if (lessThan(temp["dom(X.inner)"],X)) return "ψ_"+X.sub+"("+fund(X.inner,Y)+")"; //3.4.1
      var c=Term(temp["dom(X.inner)"]).sub; //3.4.2
      var ap=code(X.sub);
      var cp=code(c);
      var del=cp-ap-1;
      if (del>0){ //3.4.3
        if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(temp['Term(fund(X,fund(Y,"0")))'].sub,X.sub))) return "ψ_"+X.sub+"("+fund(X.inner,"ψ_"+fund(c,"0")+"("+ascend(temp['Term(fund(X,fund(Y,"0")))'].inner,del,ap)+")")+")"; //3.4.3.1
        else return "ψ_"+X.sub+"("+fund(X.inner,"ψ_"+fund(c,"0")+"(0)")+")"; //3.4.3.2
      }
      if (del<=0){ //3.4.4
        if (isNat(Y)&&(calcTemp('Term(fund(X,fund(Y,"0")))'),equal(temp['Term(fund(X,fund(Y,"0")))'].sub,X.sub))) return "ψ_"+X.sub+"("+fund(X.inner,"ψ_"+fund(c,"0")+"("+temp['Term(fund(X,fund(Y,"0")))'].inner+")")+")"; //3.4.4.1
        else return "ψ_"+X.sub+"("+fund(X.inner,"ψ_"+fund(c,"0")+"(0)")+")"; //3.4.4.2
      }
    }
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
function isStandard(x,limit){
  return findOTPath(x,limit).isStandard;
}
//ψ_0(Λ(n))
function limitOrd(n){
  return "ψ_0("+"ψ_".repeat(n+1)+"0"+"(0)".repeat(n+1)+")";
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
        }else if (cmd=="lessThanOrEqual"||cmd=="<="){
          result=lessThanOrEqual(args[0],args[1]);
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
    }else if (cmd=="lessThanOrEqual"||cmd=="<="){
      output+=result;
    }else if (cmd=="expand"){
      if (options.detail){
        for (var i=1;i<result.length;i++){
          output+=(options.abbreviate?abbreviate(result[i-1]):result[i-1])+"["+args[i]+"]="+(options.abbreviate?abbreviate(result[i]):result[i])+(i==result.length-1?"":"\n");
        }
      }else{
        output+=(options.abbreviate?abbreviate(result[result.length-1]):result[result.length-1]);
      }
    }else if (cmd=="isStandard"){
      if (options.detail){
        for (var i=1;i<result.path.length;i++){
          output+=(options.abbreviate?abbreviate(result.path[i-1]):result.path[i-1])+"["+result.funds[i]+"]="+(options.abbreviate?abbreviate(result.path[i]):result.path[i])+"\n";
        }
        if (result.isStandard) output+=(options.abbreviate?abbreviate(args[0]):args[0])+"∈OT";
        else output+=(options.abbreviate?abbreviate(args[0]):args[0])+"∉OT limited to n≦"+(args[1]||3);
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
  load();
  compute();
}
var handlekey=function(e){}
//console.log=function (s){alert(s)};
window.onerror=function (e,s,l,c,o){alert(JSON.stringify(e+"\n"+s+":"+l+":"+c+"\n"+(o&&o.stack)))};