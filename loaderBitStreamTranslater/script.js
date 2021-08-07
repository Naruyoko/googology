var lineBreakRegex=/\r?\n/g;
window.onload=function (){
  console.clear();
  dg('input').onkeydown=handlekey;
  dg('input').onfocus=handlekey;
  dg('input').onmousedown=handlekey;
  compute();
}
function dg(s){
  return document.getElementById(s);
}

function BitStream(s){
  if (!(this instanceof BitStream)) return new BitStream(s);
  if (typeof s=="undefined"||s===null){
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
BitStream.prototype.peek=function (){
  return this.stream[this.stream.length-1]==1;
}
Object.defineProperty(BitStream.prototype,"constructor",{
  value:BitStream,
  enumerable:false,
  writable:true
});

function Tree(s,t){
  if (!(this instanceof Tree)) return new Tree(s);
  if (typeof t!="undefined"&&t!==null){
    return new TreeFromPair(s,t);
  }else if (typeof s=="undefined"||s===null){
    this.leftCache=null;
    this.rightCache=null;
    this.cached=false;
  }else if (typeof s=="number"){
    return new TreeFromNumber(s);
  }else if (s instanceof BitStream){
    return new TreeFromBitStream(s);
  }else if (s instanceof Object){
    return new TreeFromPair(s,t);
  }else{
    throw Error("Invalid input");
  }
}
Tree.copyCache=function (target,source){
  if (!(target instanceof Tree)||!(source instanceof Tree)) throw Error("Expected Trees");
  target.leftCache=source.leftCache;
  target.rightCache=source.rightCache;
  target.cached=source.cached;
}
Tree.prototype.clone=function (){
  throw Error("Not implemented");
}
Tree.clone=function (x){
  if (!(x instanceof Tree)) x=new Tree(x);
  return x.clone();
}
Tree.prototype.left=function (){
  if (!this.cached) this.calculateLR();
  return this.leftCache;
}
Tree.prototype.right=function (){
  if (!this.cached) this.calculateLR();
  return this.rightCache;
}
Tree.prototype.calculateLR=function (){
  throw Error("Not implemented");
}
Tree.prototype.isNull=function (){
  return this.left()===null;
}
Tree.prototype.toNumber=function (){
  if (this.isNull()) return 0;
  else return (2*this.left().toNumber()+1)<<this.right().toNumber();
}
Tree.prototype.valueOf=function (){
  return this.toNumber();
}
Tree.prototype.equal=function (other){
  if (!(other instanceof Tree)) other=new Tree(other);
  if (this.isNull()) return other.isNull();
  else if (other.isNull()) return false;
  else return this.left().equal(other.left())&&this.right().equal(other.right());
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
Tree.prototype.writeRaw=function (nullText){
  if (this.isNull()) return typeof nullText=="undefined"?"0":nullText;
  else return "Pair("+this.left().writeRaw(nullText)+","+this.right().writeRaw(nullText)+")";
}
Tree.prototype.write=function (){
  if (this.isNull()) return "0";
  else if (this.left().isNull()){
    if (!this.right().isNull()) return "PI("+this.right().left().write()+","+this.right().right().write()+")";
    else return this.writeRaw();
  }else if (this.left().equal(Tree.ONE)){
    if (!this.right().isNull()) return "LAMBDA("+this.right().left().write()+","+this.right().right().write()+")";
    else return this.writeRaw();
  }else if (this.left().equal(Tree.TWO)){
    if (!this.right().isNull()) return "APPLY("+this.right().left().write()+","+this.right().right().write()+")";
    else return this.writeRaw();
  }else if (this.left().equal(Tree.THREE)){
    if (this.right().isNull()) return "STAR";
    else if (this.right().equal(Tree.ONE)) return "BOX";
    else return this.writeRaw();
  }else{
    if (this.right().isNull()) return "VAR "+(this.left().toNumber()/2-2);
    else return this.writeRaw();
  }
}
Tree.prototype.writeLatex=function (){
  if (this.isNull()) return "\\emptyset ";
  else if (this.left().isNull()){
    if (!this.right().isNull()) return "(\\Pi "+this.right().left().writeLatex()+"."+this.right().right().writeLatex()+")";
    else return this.writeRaw("\\emptyset ");
  }else if (this.left().equal(Tree.ONE)){
    if (!this.right().isNull()) return "(\\lambda "+this.right().left().writeLatex()+"."+this.right().right().writeLatex()+")";
    else return this.writeRaw("\\emptyset ");
  }else if (this.left().equal(Tree.TWO)){
    if (!this.right().isNull()) return "("+this.right().left().writeLatex()+"\\ "+this.right().right().writeLatex()+")";
    else return this.writeRaw("\\emptyset ");
  }else if (this.left().equal(Tree.THREE)){
    if (this.right().isNull()) return "\\ast ";
    else if (this.right().equal(Tree.ONE)) return "\\square ";
    else return this.writeRaw("\\emptyset ");
  }else{
    if (this.right().isNull()) return this.left().toNumber()/2-2+"";
    else return this.writeRaw("\\emptyset ");
  }
}
Tree.prototype.plusOne=function (){
  if (this.isNull()) return Tree.ONE;
  else if (!this.right().isNull()) return Pair(Pair(this.left(),this.right().minusOne()),Tree.ZERO);
  else return this.left().plusOne().double();
}
Tree.prototype.minusOne=function (){
  var r=this.left().double();
  for (var n=this.right().toNumber();n>=0;n--) r=Pair(r,Tree.ZERO);
  return r;
}
Tree.prototype.double=function (){
  if (this.isNull()) return this;
  else return Pair(this.left(),this.right().plusOne());
}
Tree.prototype.half=function (){
  if (this.isNull()) return this;
  else if (this.right().isNull()) return this.right();
  else return Pair(this.left(),this.right().minusOne());
}
Tree.prototype.add=function (other){
  if (typeof other=="number") return new TreeFromNumber(this.toNumber()+other);
  if (!(other instanceof Tree)) other=new Tree(other);
  return new TreeFromNumber(this.toNumber()+other.toNumber());
}
Tree.add=function (x,y){
  if (typeof x=="number"){
    if (typeof y=="number") return new TreeFromNumber(x+y);
    if (!(y instanceof Tree)) y=new Tree(y);
    return new TreeFromNumber(x+y.toNumber());
  }else{
    if (!(x instanceof Tree)) x=new Tree(x);
    if (typeof y=="number") return new TreeFromNumber(x.toNumber()+y);
    if (!(y instanceof Tree)) y=new Tree(y);
    return new TreeFromNumber(x.toNumber()+y.toNumber());
  }
}
Tree.prototype.sub=function (other){
  if (typeof other=="number") return new TreeFromNumber(this.toNumber()-other);
  if (!(other instanceof Tree)) other=new Tree(other);
  return new TreeFromNumber(this.toNumber()-other.toNumber());
}
Tree.sub=function (x,y){
  if (typeof x=="number"){
    if (typeof y=="number") return new TreeFromNumber(x-y);
    if (!(y instanceof Tree)) y=new Tree(y);
    return new TreeFromNumber(x-y.toNumber());
  }else{
    if (!(x instanceof Tree)) x=new Tree(x);
    if (typeof y=="number") return new TreeFromNumber(x.toNumber()-y);
    if (!(y instanceof Tree)) y=new Tree(y);
    return new TreeFromNumber(x.toNumber()-y.toNumber());
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

function TreeFromNumber(s){
  if (!(this instanceof TreeFromNumber)) return new TreeFromNumber(s);
  Tree.call(this);
  if (typeof s=="undefined"||s===null){
    this.numberValue=0;
  }else if (typeof s=="number"){
    this.numberValue=s;
  }else if (s instanceof TreeFromNumber){
    Tree.copyCache(this,s);
    this.numberValue=s.numberValue;
  }else{
    throw Error("Invalid input");
  }
}
Object.assign(TreeFromNumber,Tree);
TreeFromNumber.prototype=Object.create(Tree.prototype);
TreeFromNumber.prototype.clone=function (){
  return new TreeFromNumber(this);
}
TreeFromNumber.prototype.calculateLR=function (){
  if (this.numberValue===0){
    this.leftCache=null;
    this.rightCache=null;
  }else{
    var left=this.numberValue;
    var right=0;
    while ((left&1)==0){
      left>>=1;
      right++;
    }
    this.leftCache=new TreeFromNumber(left>>1);
    this.rightCache=new TreeFromNumber(right);
  }
  this.cached=true;
}
TreeFromNumber.prototype.isNull=function (){
  return this.numberValue===0;
}
TreeFromNumber.prototype.toNumber=function (){
  return this.numberValue;
}
TreeFromNumber.prototype.equal=function (other){
  if (typeof other=="number") return this.numberValue==other;
  if (other instanceof TreeFromNumber) return this.numberValue==other.numberValue;
  return Tree.prototype.equal.call(this,other);
}
Object.defineProperty(TreeFromNumber.prototype,"constructor",{
  value:TreeFromNumber,
  enumerable:false,
  writable:true
});

function TreeFromBitStream(s){
  if (!(this instanceof TreeFromBitStream)) return new TreeFromBitStream(s);
  Tree.call(this);
  if (typeof s=="undefined"||s===null){
    this.bitstreamValue=new BitStream();
  }else if (s instanceof BitStream){
    this.bitstreamValue=s.clone();
  }else if (s instanceof TreeFromBitStream){
    Tree.copyCache(this,s);
    this.bitstreamValue=s.bitstreamValue;
  }else{
    throw Error("Invalid input");
  }
}
Object.assign(TreeFromBitStream,Tree);
TreeFromBitStream.prototype=Object.create(Tree.prototype);
TreeFromBitStream.prototype.clone=function (){
  return new TreeFromBitStream(this);
}
TreeFromBitStream.prototype.calculateLR=function (){
  if (this.bitstreamValue.isZero()){
    this.leftCache=null;
    this.rightCache=null;
  }else{
    var left=this.bitstreamValue.clone();
    var right=0;
    while (left.next()==0) right++;
    this.left=new TreeFromBitStream(left);
    this.right=new TreeFromNumber(right);
  }
  this.cached=true;
}
TreeFromBitStream.prototype.isNull=function (){
  return this.bitstreamValue.isZero();
}
TreeFromBitStream.prototype.toNumber=function (){
  return this.bitstreamValue.toNumber();
}
TreeFromBitStream.prototype.equal=function (other){
  if (typeof other=="number") return this.bitstreamValue.equal(other);
  if (other instanceof TreeFromBitStream) return this.bitstreamValue.equal(other.bitstreamValue);
  return Tree.prototype.equal.call(this,other);
}
Object.defineProperty(TreeFromBitStream.prototype,"constructor",{
  value:TreeFromBitStream,
  enumerable:false,
  writable:true
});

function TreeFromPair(s,t){
  if (!(this instanceof TreeFromPair)) return new TreeFromPair(s,t);
  Tree.call(this);
  if (typeof t=="undefined"||t===null){
    if (typeof s=="undefined"||s===null){
      this.leftInput=null;
      this.rightInput=null;
      this.wasInputNull=true;
    }else if (s instanceof Array){
      this.leftInput=s[0];
      this.rightInput=s[1];
      this.wasInputNull=false;
    }else if (s instanceof TreeFromPair){
      this.leftInput=s.leftInput;
      this.rightInput=s.rightInput;
      Tree.copyCache(this,s);
      this.wasInputNull=false;
    }else if (s instanceof Tree){
      this.leftInput=s.left();
      this.rightInput=s.right();
      Tree.copyCache(this,s);
      this.wasInputNull=false;
    }else if (s instanceof Object){
      this.leftInput=s.left;
      this.rightInput=s.right;
      this.wasInputNull=false;
    }else{
      throw Error("Invalid input");
    }
  }else{
    if (s===null&&t!==null||s!==null&&t===null) throw Error("Invalid input");
    this.leftInput=s;
    this.rightInput=t;
    this.wasInputNull=false;
  }
}
Object.assign(TreeFromPair,Tree);
TreeFromPair.prototype=Object.create(Tree.prototype);
TreeFromPair.prototype.clone=function (){
  return new TreeFromPair(this);
}
TreeFromPair.prototype.calculateLR=function (){
  if (this.wsInputNull){
    this.leftCache=null;
    this.rightCache=null;
  }else{
    this.leftCache=new Tree(this.leftInput);
    this.rightCache=new Tree(this.rightInput);
  }
  this.cached=true;
}
Object.defineProperty(TreeFromPair.prototype,"constructor",{
  value:TreeFromPair,
  enumerable:false,
  writable:true
});

Tree.ZERO=new Tree(0);
Tree.ONE=new Tree(1);
Tree.TWO=new Tree(2);
Tree.THREE=new Tree(3);
Tree.STAR=new Tree(7);
Tree.BOX=new Tree(14);
Tree.VAR0=new Tree(9);
Tree.VAR1=new Tree(13);

function Pair(x,y){
  return new TreeFromPair(x,y);
}
function Left(x){
  if (!(x instanceof Tree)) x=new Tree(x);
  if (x.isNull()){
    return Tree.ZERO;
  }else{
    return x.left();
  }
}
function Right(x){
  if (!(x instanceof Tree)) x=new Tree(x);
  return x.isNull()?Tree.ZERO:x.right();
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
      if (aux.equal(vv)) return yy;
      else{
        if (aux.toNumber()>vv) return new Tree(term.toNumber()-context);
        else return term;
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
var deriveCache=new Map();
// Returns [theorem,proofs,proofs as bit streams,xx,consumed bit stream,formatted consumed bit stream,is proof empty]
// A proof is an array of lines, each line being [theorem,comment]
function DeriveDetail(xx,proofs,proofsAsBitStreams){
  if (!(xx instanceof BitStream)) xx=new BitStream(xx);
  var isTheMainTheorem=typeof proofs=="undefined";
  if (isTheMainTheorem){
    proofs=[];
    proofsAsBitStreams=[];
  }
  if (!(proofs instanceof Array)||!(proofsAsBitStreams instanceof Array)) throw Error("Something went wrong... A non-Array was passed to proofs");
  var bitStreamIn=xx.stream;
  if (isTheMainTheorem&&deriveCache.has(bitStreamIn)) return deriveCache.get(bitStreamIn);
  var proof=[];
  var auxType;
  var auxTerm;
  var context=Tree.ZERO;
  var term=Tree.STAR; //7
  var type=Tree.BOX; //14
  var consumedBitStream="";
  var formattedBitStream="";
  var isProofEmpty=true;
  var theorem=Tree.ZERO;
  function nextBit(){
    var bit=xx.next();
    consumedBitStream=+bit+consumedBitStream;
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
    var subResult=DeriveDetail(xx,proofs,proofsAsBitStreams);
    var lemma=subResult[0];
    auxTerm=Left(lemma);
    auxType=Left(/*lastRight*/Right(lemma));
    //Since the same bit stream object is passed, there's no need to recover this
    //xx=Left(/*lastRight*/Right(Right(lemma)));
    //xx=subResult[3];
    //Same for proofs
    //proofs=subResult[1];
    //proofsAsBitStreams=subResult[2];
    var lemmaCount=proofs.length;
    var commentAppend;
    consumedBitStream=subResult[4]+consumedBitStream;
    if (subResult[6]){
      formattedBitStream="["+subResult[5]+"]"+formattedBitStream;
      commentAppend=" (axiom)";
    }else{
      formattedBitStream="["+subResult[5]+"]_{("+lemmaCount+")}"+formattedBitStream;
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
  if (isTheMainTheorem||!isProofEmpty){
    proofs.push(proof);
    proofsAsBitStreams.push(consumedBitStream);
  }
  var r=[theorem,proofs,proofsAsBitStreams,xx,consumedBitStream,formattedBitStream,isProofEmpty];
  if (isTheMainTheorem) deriveCache.set(bitStreamIn,r);
  return r;
}

function writeContext(context){
  if (!(context instanceof Tree)) context=new Tree(context);
  var contextText="";
  while (!context.isNull()){
    contextText=Left(context).writeLatex()+contextText;
    context=Right(context);
    if (!context.isNull()) contextText=","+contextText;
  }
  return contextText;
}

function formatProofWithLatex(input,contractSameProofs){
  if (typeof input=="number"||input instanceof BitStream) input=DeriveDetail(input);
  if (!(input instanceof Array)) throw Error("Something went wrong...");
  if (typeof contractSameProofs=="undefined") contractSameProofs=false;
  var theorem=input[0];
  var proofs=input[1];
  var proofsAsBitStreams=input[2];
  var xx=input[3];
  var consumedBitStream=input[4];
  var formattedBitStream=input[5];
  var isProofEmpty=input[6];
  var theoremNumMap=[];
  if (contractSameProofs){
    var theoremMap=new Map();
    for (var i=0;i<proofs.length;i++){
      var theoremNum;
      if (theoremMap.has(proofsAsBitStreams[i])) theoremNum=theoremMap.get(proofsAsBitStreams[i]);
      else theoremMap.set(proofsAsBitStreams[i],theoremNum=theoremMap.size);
      theoremNumMap.push(theoremNum);
    }
  }else{
    for (var i=0;i<proofs.length;i++) theoremNumMap.push(i);
  }
  var bitStreamInfo=(xx.isZero()?"":"{\\color{lightgray}"+xx.toString()+"}")+formattedBitStream.replace(/\((\d+)\)/g,function (s,num){return "("+(theoremNumMap[num-1]+1)+")";});
  var proofBody="\\begin{align}";
  var theoremsPrinted=0;
  for (var proofi=0;proofi<proofs.length;proofi++){
    if (theoremNumMap[proofi]<theoremsPrinted) continue;
    var proof=proofs[proofi];
    for (var linei=0;linei<proof.length;linei++){
      var line=proof[linei];
      proofBody+="\n";
      var isLastLineOfLemma=linei==proof.length-1&&proofi<proofs.length-1;
      if (isLastLineOfLemma) proofBody+="("+(theoremNumMap[proofi]+1)+") ";
      proofBody+="&\\quad &";
      var term=Left(line[0]);
      var type=Left(Right(line[0]));
      var context=Right(Right(Right(line[0])));
      proofBody+=writeContext(context)+"&\\vdash "+term.writeLatex()+":"+type.writeLatex()+"&\\quad &\\text{"+line[1].replace(/\((\d+)\)/,function (s,num){return "("+(theoremNumMap[num-1]+1)+")";})+"} \\\\";
      if (isLastLineOfLemma) proofBody+="\n\\\\";
    }
    theoremsPrinted++;
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
  var bitStreams=[""];
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
      if (bitStreams[bitStreams.length-1]) bitStreams.push("");
      bitStreams[bitStreams.length-1]+=blocks.shift();
      scopes.shift();
      wordIndex++;
    }else if (word.type=="word"){
      var expanding=[word];
      for (var i=0;i<expanding.length;i++){
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
      else bitStreams[bitStreams.length-1]+=processed;
      wordIndex++;
    }else if (word.type=="newLine"){
      if (bitStreams[bitStreams.length-1]) bitStreams.push("");
      wordIndex++;
    }else{
      wordIndex++;
    }
  }
  if (!bitStreams[bitStreams.length-1]) bitStreams.pop();
  return bitStreams.map(BitStream);
}
var proofCache=new Map();
var outDOMCacheSize=100;
var outDOMCache=new Array(outDOMCacheSize);
var outDOMCacheAccesses=0;
var input="";
var contractSameProofs=true;
var lastBitStreams="";
function compute(){
  if (input==dg("input").value&&contractSameProofs==dg("contractSameProofs").checked) return;
  input=dg("input").value;
  var bitStreams;
  try{
    bitStreams=compileInput(input);
  }catch(e){
    lastBitStreams="";
    dg("output").innerHTML=(e.stack?e.stack:e).replace(lineBreakRegex,"<br>");
    console.error(e);
    return;
  }
  if (lastBitStreams==bitStreams.map(function (e){return e.stream+";";}).join("")&&contractSameProofs==dg("contractSameProofs").checked) return;
  contractSameProofs=dg("contractSameProofs").checked;
  lastBitStreams=bitStreams.map(function (e){return e.stream+";";}).join("");
  dg("output").innerHTML="";
  var newNodes=[];
  for (var i=0;bitStreams&&i<bitStreams.length;i++){
    var exceptionThrown=null;
    var bitStreamIn=bitStreams[i].stream;
    var bitStreamWithOptionID=bitStreamIn+contractSameProofs
    try{
      var formattedProof=null;
      var insertIndex=0;
      for (var j=0;j<outDOMCacheSize;j++){
        if (outDOMCache[j]&&outDOMCache[j][1]==bitStreamWithOptionID){
          formattedProof=outDOMCache[j][2];
          outDOMCache[j][0]=outDOMCacheAccesses;
          break;
        }else if (outDOMCache[insertIndex]&&(!outDOMCache[j]||outDOMCache[j][0]<outDOMCache[insertIndex][0])){
          insertIndex=j;
        }
      }
      if (!formattedProof){
        if (proofCache.has(bitStreamWithOptionID)) formattedProof=proofCache.get(bitStreamIn);
        else proofCache.set(bitStreamWithOptionID,formattedProof=formatProofWithLatex(DeriveDetail(bitStreams[i]),contractSameProofs));
      }
    }catch(e){
      exceptionThrown=e;
      var node=document.createElement("div");
      node.classList.add("proofcontainer");
      node.innerHTML="Error processing "+bitStreams[i].stream+"<br>&darr;HERE<br>"+bitStreamIn.substring(bitStreams[i].stream.length)+"<br>"+(e.stack?e.stack:e).replace(lineBreakRegex,"<br>");
      dg("output").appendChild(node);
      console.error(e);
    }finally{
      if (!exceptionThrown){
        var node;
        if (formattedProof instanceof Node){
          node=formattedProof;
        }else if (formattedProof instanceof Array){
          var nodeInnerHTML="";
          for (var j=0;j<formattedProof.length;j++){
            nodeInnerHTML+="\\("+formattedProof[j]+"\\)<br>";
          }
          node=document.createElement("div");
          node.classList.add("proofcontainer");
          node.innerHTML=nodeInnerHTML;
          newNodes.push(node);
          outDOMCache.splice(insertIndex,1,[outDOMCacheAccesses,bitStreamWithOptionID,node]);
        }else throw Error("Something went wrong...");
        dg("output").appendChild(node);
      }
      outDOMCacheAccesses++;
    }
  }
  /*var debugDiv=document.createElement("div");
  debugDiv.innerHTML=outDOMCache.map(e=>e?e[0]+" "+e[1]:"empty").join("<br>");
  dg("output").appendChild(debugDiv);*/
  // Modified a sample from https://docs.mathjax.org/en/latest/web/typeset.html
  if (newNodes.length) MathJax.startup.promise = MathJax.startup.promise
    .then(function() {return MathJax.typesetPromise(newNodes);})
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