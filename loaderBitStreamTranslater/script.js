var lineBreakRegex=/\r?\n/g;
window.onload=function (){
  console.clear();
  dg('input').onkeydown=handlekey;
  dg('input').onfocus=handlekey;
  dg('input').onmousedown=handlekey;
}
function dg(s){
  return document.getElementById(s);
}

function BitStream(s){
  if (!(this instanceof BitStream)) return new BitStream(s);
  if (typeof s=="undefined"){
    this.stream="";
  }else if (typeof s=="number"){
    this.stream=s===0?"":Math.floor(s).toString(2);
  }else if (typeof s=="bigint"||s instanceof bigInt){
    this.stream=s==0?"":s.toString(2);
  }else if (typeof s=="string"){
    this.stream=s.replace(/[^01]/g,"").replace(/^0+/,"");
  }else if (s instanceof BitStream){
    this.stream=s.stream;
  }else{
    throw Error("Invalid input");
  }
}
BitStream.prototype.clone=function (){
  return new BitStream(this);
}
BitStream.clone=function (x){
  return x.clone();
}
BitStream.prototype.toNumber=function (){
  return parseInt(this.stream,"2");
}
BitStream.prototype.toString=function (){
  return this.stream;
}
BitStream.prototype.isZero=function (){
  return this.stream.length===0;
}
BitStream.prototype.next=function (){
  var bit=this.stream[this.stream.length-1]==1;
  this.stream=this.stream.substring(0,this.stream.length-1);
  return bit;
}
Object.defineProperty(BitStream.prototype,"constructor",{
  value:BitStream,
  enumerable:false,
  writable:true
});

function Tree(s){
  if (!(this instanceof Tree)) return new Tree(s);
  if (typeof s=="undefined"||s===null){
    this.left=null;
    this.right=null;
  }else if (typeof s=="number"){
    if (s==0){
      this.left=null;
      this.right=null;
    }else{
      var left=s;
      var right=0;
      while ((left&1)==0){
        left>>=1;
        right++;
      }
      this.left=new Tree(left>>1);
      this.right=new Tree(right);
    }
  }else if (s instanceof Array){
    this.left=new Tree(s[0]);
    this.right=new Tree(s[1]);
  }else if (s instanceof BitStream){
    if (s.isZero()){
      this.left=null;
      this.right=null;
    }else{
      var left=s.clone();
      var right=0;
      while (left.next()==0) right++;
      this.left=new Tree(s.toNumber());
      this.right=new Tree(right);
    }
  }else if (s instanceof Tree){
    if (s.isNull()){
      this.left=null;
      this.right=null;
    }else{
      this.left=s.left.clone();
      this.right=s.right.clone();
    }
  }else if (s instanceof Object){
    this.left=new Tree(s.left);
    this.right=new Tree(s.right);
  }else{
    throw Error("Invalid input");
  }
}
Tree.prototype.clone=function (){
  return new Tree(this);
}
Tree.clone=function (x){
  if (!(x instanceof Tree)) x=new Tree(x);
  return x.clone();
}
Tree.prototype.isNull=function (){
  return this.left===null;
}
Tree.prototype.toNumber=function (){
  if (this.isNull()) return 0;
  else return (2*this.left.toNumber()+1)<<this.right.toNumber();
}
Tree.prototype.valueOf=function (){
  return this.toNumber();
}
Tree.prototype.writeRaw=function (){
  if (this.isNull()) return "0";
  else return "Pair("+this.left.writeRaw()+","+this.right.writeRaw()+")";
}
Tree.prototype.write=function (){
  if (this.isNull()) return "0";
  else if (this.left.isNull()){
    if (!this.right.isNull()) return "PI("+this.right.left.write()+","+this.right.right.write()+")";
    else return this.writeRaw();
  }else if (this.left.equal(Tree.ONE)){
    if (!this.right.isNull()) return "LAMBDA("+this.right.left.write()+","+this.right.right.write()+")";
    else return this.writeRaw();
  }else if (this.left.equal(Tree.TWO)){
    if (!this.right.isNull()) return "APPLY("+this.right.left.write()+","+this.right.right.write()+")";
    else return this.writeRaw();
  }else if (this.left.equal(Tree.THREE)){
    if (this.right.isNull()) return "STAR";
    else if (this.right.equal(Tree.ONE)) return "BOX";
    else return this.writeRaw();
  }else{
    if (this.right.isNull()) return "VAR "+(this.left.toNumber()/2-2);
    else return this.writeRaw();
  }
}
Tree.prototype.writeLatex=function (){
  if (this.isNull()) return "0";
  else if (this.left.isNull()){
    if (!this.right.isNull()) return "(\\Pi "+this.right.left.writeLatex()+"."+this.right.right.writeLatex()+")";
    else return this.writeRaw();
  }else if (this.left.equal(Tree.ONE)){
    if (!this.right.isNull()) return "(\\lambda "+this.right.left.writeLatex()+"."+this.right.right.writeLatex()+")";
    else return this.writeRaw();
  }else if (this.left.equal(Tree.TWO)){
    if (!this.right.isNull()) return "("+this.right.left.writeLatex()+"\\ "+this.right.right.writeLatex()+")";
    else return this.writeRaw();
  }else if (this.left.equal(Tree.THREE)){
    if (this.right.isNull()) return "\\ast ";
    else if (this.right.equal(Tree.ONE)) return "\\square ";
    else return this.writeRaw();
  }else{
    if (this.right.isNull()) return this.left.toNumber()/2-2+"";
    else return this.writeRaw();
  }
}
Tree.prototype.equal=function (other){
  if (!(other instanceof Tree)) other=new Tree(other);
  if (this.isNull()) return other.isNull();
  else if (other.isNull()) return false;
  else return this.left.equal(other.left)&&this.right.equal(other.right);
}
Tree.equal=function (x,y){
  if (!(x instanceof Tree)) x=new Tree(x);
  if (!(y instanceof Tree)) y=new Tree(y);
  return x.equal(y);
}
Tree.prototype.notEqual=function (other){
  return !this.equal(other);
}
Tree.notEqual=function (x,y){
  if (!(x instanceof Tree)) x=new Tree(x);
  if (!(y instanceof Tree)) y=new Tree(y);
  return x.notEqual(y);
}
Tree.ZERO=new Tree(0);
Tree.ONE=new Tree(1);
Tree.TWO=new Tree(2);
Tree.THREE=new Tree(3);
Tree.STAR=new Tree(7);
Tree.BOX=new Tree(14);
Tree.VAR0=new Tree(9);
Tree.VAR1=new Tree(13);
Tree.prototype.plusOne=function (){
  if (this.isNull()) return Tree.ONE.clone();
  else if (!this.right.isNull()) return Pair(Pair(this.left,this.right.minusOne()),Tree.ZERO);
  else return this.left.plusOne().double();
}
Tree.prototype.minusOne=function (){
  var r=this.left.double();
  for (var n=+this.right;n>=0;n--) r=Pair(r,Tree.ZERO);
  return r;
}
Tree.prototype.double=function (){
  if (this.isNull()) return this.clone();
  else return Pair(this.left,this.right.plusOne());
}
Tree.prototype.half=function (){
  if (this.isNull()) return this.clone();
  else if (this.right.isNull()) return this.right.clone();
  else return Pair(this.left,this.right.minusOne());
}
Tree.prototype.add=function (other){
  if (typeof other=="number") return new Tree(this.toNumber()+other);
  if (!(other instanceof Tree)) other=new Tree(other);
  return new Tree(this.toNumber()+other.toNumber());
}
Tree.add=function (x,y){
  if (typeof x=="number"){
    if (typeof y=="number") return new Tree(x+y);
    if (!(y instanceof Tree)) y=new Tree(y);
    return new Tree(x+y.toNumber());
  }else{
    if (!(x instanceof Tree)) x=new Tree(x);
    if (typeof y=="number") return new Tree(x.toNumber()+y);
    if (!(y instanceof Tree)) y=new Tree(y);
    return new Tree(x.toNumber()+y.toNumber());
  }
}
Tree.prototype.sub=function (other){
  if (typeof other=="number") return new Tree(this.toNumber()-other);
  if (!(other instanceof Tree)) other=new Tree(other);
  return new Tree(this.toNumber()-other.toNumber());
}
Tree.sub=function (x,y){
  if (typeof x=="number"){
    if (typeof y=="number") return new Tree(x-y);
    if (!(y instanceof Tree)) y=new Tree(y);
    return new Tree(x-y.toNumber());
  }else{
    if (!(x instanceof Tree)) x=new Tree(x);
    if (typeof y=="number") return new Tree(x.toNumber()-y);
    if (!(y instanceof Tree)) y=new Tree(y);
    return new Tree(x.toNumber()-y.toNumber());
  }
}
Tree.prototype.shiftLeft=function (other){
  return Pair(this.half(),other);
}
Tree.shiftLeft=function (x,y){
  if (!(x instanceof Tree)) x=new Tree(x);
  return x.shiftLeft(y);
}
Object.defineProperty(Tree.prototype,"constructor",{
  value:Tree,
  enumerable:false,
  writable:true
});

function Pair(x,y){
  return new Tree([x,y]);
}
function Left(x){
  if (!(x instanceof Tree)) x=new Tree(x);
  if (x.isNull()){
    return Tree.ZERO;
  }else{
    return x.left;
  }
}
function Right(x){
  if (!(x instanceof Tree)) x=new Tree(x);
  return x.isNull()?Tree.ZERO:x.right;
}

function Subst(vv,yy,context,term){
  if (!(yy instanceof Tree)) yy=new Tree(yy);
  if (!(term instanceof Tree)) yy=new Tree(term);
  var aux=Left(term);
  var xx=/*lastRight*/Right(term);
  if (aux.equal(Tree.TWO)){
    return Apply(Subst(vv,yy,context,Left(xx)),
                 Subst(vv,yy,context,Right(xx)));
  }else{
    if (aux.toNumber()>2){
      if (aux.equal(vv)) return yy.clone();
      else{
        if (aux.toNumber()>vv) return new Tree(term.toNumber()-context);
        else return term.clone();
      } 
    }else
      return Pair(aux,Pair(Subst(vv,yy,context,Left(xx)),
                           Subst(vv+2,Lift(yy),context,Right(xx))));
  }
}
function Lift(xx){
  return Subst(4,Tree.VAR1,-4,xx);
}
function Apply(yy,xx){
  if (!(yy instanceof Tree)) yy=new Tree(yy);
  if (!(xx instanceof Tree)) xx=new Tree(xx);
  if (Left(yy).equal(Tree.ONE)) return Subst(4,xx,4,Right(/*lastRight*/Right(yy)));
  else return Pair(Tree.TWO,Pair(yy,xx));
}
// Returns [theorem,proofs,xx,formatted consumed bit stream,is proof empty]
// A proof is an array of lines, each line being [theorem,comment]
function DeriveDetail(xx,proofs){
  if (!(xx instanceof BitStream)) xx=new BitStream(xx);
  var isTheMainTheorem=typeof proofs=="undefined";
  if (isTheMainTheorem) proofs=[];
  if (!(proofs instanceof Array)) throw Error("Something went wrong... A non-Array was passed to proofs");
  var proof=[];
  var auxType;
  var auxTerm;
  var context=Tree.ZERO;
  var term=Tree.STAR; //7
  var type=Tree.BOX; //14
  var formattedBitStream="";
  var isProofEmpty=true;
  var theorem=Tree.ZERO;
  function nextBit(){
    var bit=xx.next();
    formattedBitStream=+bit+formattedBitStream;
    return bit;
  }
  function pushLine(comment){
    proof.push([theorem=Pair(term,Pair(type,Pair(/*xx*/Tree.ZERO,context))),comment]);
    isProofEmpty=false;
  }
  pushLine("axiom");
  isProofEmpty=true;
  while (nextBit()){
    var subResult=DeriveDetail(xx,proofs);
    var lemma=subResult[0];
    auxTerm=Left(lemma);
    auxType=Left(/*lastRight*/Right(lemma));
    //Since the same bit stream object is passed, there's no need to recover this
    //xx=Left(/*lastRight*/Right(Right(lemma)));
    //xx=subResult[2];
    //Same for proofs
    //proofs=subResult[1];
    var lemmaCount=proofs.length;
    var commentAppend;
    if (subResult[4]){
      formattedBitStream="["+subResult[3]+"]"+formattedBitStream;
      commentAppend=" (axiom)";
    }else{
      formattedBitStream="["+subResult[3]+"]_{("+lemmaCount+")}"+formattedBitStream;
      commentAppend=" ("+lemmaCount+")";
    }
    if (context.equal(/*lastRight*/Right(Right(Right(lemma))))){
      if (Left(type).isNull()&&Left(/*lastRight*/Right(type)).equal(auxType)&&nextBit()){
        type=Subst(4,auxTerm,4,/*lastRight*/Right(Right(type)));
        term=Apply(term,auxTerm);
        pushLine("application"+commentAppend);
      }
      if (nextBit()&&(auxType.equal(Tree.STAR)||auxType.equal(Tree.BOX))){
        context=Pair(auxTerm,context);
        term=Lift(term);
        type=Lift(type);
        pushLine("weakening"+commentAppend);
      }
    }
    if (!context.isNull()&&nextBit()){
      if (nextBit()||!(type.equal(Tree.STAR)||type.equal(Tree.BOX))){
        term=Pair(Tree.ONE,Pair(Left(context),term));
        type=Pair(Tree.ZERO,Pair(Left(context),type));
        context=/*lastRight*/Right(context);
        pushLine("abstraction");
      }else{
        term=Pair(Tree.ZERO,Pair(Left(context),term));
        context=/*lastRight*/Right(context);
        pushLine("formation");
      }
    }
    if (nextBit()&&(type.equal(Tree.STAR)||type.equal(Tree.BOX))){
      context=Pair(term,context);
      type=Lift(term);
      term=Tree.VAR0;
      pushLine("variable");
    }
  }
  if (isTheMainTheorem||!isProofEmpty) proofs.push(proof);
  return [theorem,proofs,xx,formattedBitStream,isProofEmpty];
}

function formatProofWithLatex(input){
  if (typeof input=="number"||input instanceof BitStream) input=DeriveDetail(input);
  if (!(input instanceof Array)) throw Error("Something went wrong...");
  var theorem=input[0];
  var proofs=input[1];
  var xx=input[2];
  var formattedBitStream=input[3];
  var isProofEmpty=input[4];
  var bitStreamInfo=(xx.isZero()?"":"{\\color{lightgray}"+xx.toString()+"}")+formattedBitStream;
  var proofBody="\\begin{align}";
  for (var proofi=0;proofi<proofs.length;proofi++){
    var proof=proofs[proofi];
    for (var linei=0;linei<proof.length;linei++){
      var line=proof[linei];
      proofBody+="\n";
      var isLastLineOfLemma=linei==proof.length-1&&proofi<proofs.length-1;
      if (isLastLineOfLemma) proofBody+="("+(proofi+1)+") ";
      proofBody+="&\\quad &";
      var term=Left(line[0]);
      var type=Left(Right(line[0]));
      var context=Right(Right(Right(line[0])));
      var contextText="";
      while (!context.isNull()){
        contextText=Left(context).writeLatex()+contextText;
        context=Right(context);
        if (!context.isNull()) contextText=","+contextText;
      }
      proofBody+=contextText+"&\\vdash "+term.writeLatex()+":"+type.writeLatex()+"&\\quad &\\text{"+line[1]+"} \\\\";
      if (isLastLineOfLemma) proofBody+="\n\\\\";
    }
  }
  proofBody+="\n\\end{align}";
  return [bitStreamInfo,proofBody];
}


function compileInput(s){
  var wordRegex=/[^\t \(\)]+|[\(\)]/g;
  var lines=s.split(lineBreakRegex);
  var wordStream=[];
  for (var linen=0;linen<lines.length;linen++){
    var wordsInLine=lines[linen].match(wordRegex);
    var isLineEmpty=true;
    for (var i=0;wordsInLine&&i<wordsInLine.length;i++){
      if (wordsInLine[i]){
        if (wordsInLine[i][0]=="("){
          wordStream.push({
            type:"lParen"
          });
        }else if (wordsInLine[i][0]==")"){
          wordStream.push({
            type:"rParen"
          });
        }else{
          wordStream.push({
            type:"word",
            content:wordsInLine[i]
          });
        }
        isLineEmpty=false;
      }
    }
    if (!isLineEmpty) wordStream.push({
      type:"newLine"
    });
  }
  var scopes=[{macros:{}}];
  var blocks=[];
  var bitStreams=[];
  var wordIndex=0;
  while (wordIndex<wordStream.length){
    var word=wordStream[wordIndex];
    if (word.type=="word"&&word.content=="define"){
      var name=wordStream[++wordIndex].content;
      if (!name||/^[0-9]/.test(name)) throw Error(name+" is an invalid alias");
      scopes[0].macros[name]=[];
      while (wordStream[++wordIndex]&&wordStream[wordIndex].type!="newLine"){
        scopes[0].macros[name].push(wordStream[wordIndex]);
      }
      wordIndex++;
    }else if (word.type=="word"&&word.content=="undef"){
      var name=wordStream[++wordIndex].content;
      if (!name||/^[0-9]/.test(name)) throw Error(name+" is an invalid alias");
      scopes[0].macros[name]=undefined;
      wordIndex++;
    }else if (word.type=="word"&&word.content=="start"){
      blocks.unshift("");
      scopes.unshift({macros:{}});
      wordIndex++;
    }else if (word.type=="word"&&word.content=="end"){
      bitStreams.push(blocks.shift());
      scopes.shift();
      wordIndex++;
    }else if (word.type=="word"){
      var expanding=[word];
      for (var i=0;console.log(expanding),i<expanding.length;i++){
        for (var scopeDepth=0;scopeDepth<scopes.length;scopeDepth++){
          if (typeof scopes[scopeDepth].macros[expanding[i].content]!="undefined"){
            expanding.splice(i,1,...scopes[scopeDepth].macros[expanding[i].content]);
            i--;
            break;
          }
        }
      }
      var processed="";
      for (var i=0;i<expanding.length;i++){
        var header=expanding[i].content.substring(0,2);
        if (header=="0b"){
          processed+=expanding[i].content.substring(2).replace(/[^01]/g,"");
        }else if (header=="0o"){
          processed+=bigInt(header+(expanding[i].content.length<=2?header+"0":expanding[i].content.substring(2)).replace(/[^0-7]/g,"")).toString(2);
        }else if (header=="0x"){
          processed+=bigInt(header+(expanding[i].content.length<=2?header+"0":expanding[i].content.substring(2)).replace(/[^0-9A-Fa-f]/g,"")).toString(2);
        }else if (header=="0d"){
          processed+=bigInt((expanding[i].content.length<=2?header+"0":expanding[i].content.substring(2)).replace(/[^0-9]/g,"")).toString(2);
        }else{
          processed+=expanding[i].content.replace(/[^01]/g,"");
        }
      }
      if (blocks.length) blocks[0]+=processed;
      else bitStreams.push(processed);
      wordIndex++;
    }else{
      wordIndex++;
    }
  }
  return bitStreams.map(BitStream);
}
var input="";
function compute(){
  if (input==dg("input").value) return;
  input=dg("input").value;
  var output="";
  var bitStreams;
  try{
    bitStreams=compileInput(input);
  }catch(e){
    output+=(e.stack?e.stack:e).replace(lineBreakRegex,"<br>");
  }
  for (var i=0;bitStreams&&i<bitStreams.length;i++){
    var exceptionThrown=null;
    try{
      var formattedProof=formatProofWithLatex(DeriveDetail(bitStreams[i]));
    }catch(e){
      exceptionThrown=e;
      output+="<div class=\"proofcontainer\">"+(e.stack?e.stack:e).replace(lineBreakRegex,"<br>")+"</div>";
    }finally{
      if (!exceptionThrown){
        output+="<div class=\"proofcontainer\">";
        for (var j=0;j<formattedProof.length;j++){
          output+="\\("+formattedProof[j]+"\\)<br>";
        }
        output+="</div>";
      }
    }
  }
  dg("output").innerHTML=output;
  // Modified a sample from https://docs.mathjax.org/en/latest/web/typeset.html
  MathJax.startup.promise = MathJax.startup.promise
    .then(function() {return MathJax.typesetPromise([dg("output")]);})
    .catch(function(err) {console.log('Typeset failed: ' + err.message);});
}
window.onpopstate=function (e){
  load();
  computeIfAuto();
}
var handlekey=function(e){
  if (dg("auto").checked) compute();
}
//console.log=function (s){alert(s)};
window.onerror=function (e,s,l,c,o){alert(JSON.stringify(e+"\n"+s+":"+l+":"+c+"\n"+(o&&o.stack)))};