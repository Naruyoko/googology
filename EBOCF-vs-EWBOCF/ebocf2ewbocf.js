var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ,]/g;
window.onload=function (){
  console.clear();
  document.getElementById('input').onkeydown=handlekey;
  document.getElementById('input').onfocus=handlekey;
  document.getElementById('input').onmousedown=handlekey;
  convertall();
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
 * @typedef {{left:BuchholzTerm,right:BuchholzTerm}} BuchholzPTerm
 * @typedef {BuchholzPTerm|BuchholzPTerm[]} BuchholzTerm
 * @typedef {0|{left:WeakTerm,right:WeakTerm}} WeakTerm
 */

/**
 * @param {string|Scanner} s 
 * @param {number=} context 
 * @returns {BuchholzTerm}
 */
function parseBuchholz(s,context){
  /** @param {BuchholzTerm} term */
  function appendToRSum(term){
    if (state==START) r=term;
    else if (state==PLUS){
      if (term instanceof Array){
        if (r instanceof Array) r=r.concat(term);
        else r=[r].concat(term);
      }else{
        if (r instanceof Array) r.push(term);
        else r=[r,term];
      }
    }else throw Error("Wrong state when attempting to append as sum");
    state=CLOSEDTERM;
  }
  var scanner;
  if (typeof s=="string") scanner=new Scanner(s);
  else if (s instanceof Scanner) scanner=s;
  else throw Error("Invalid expression: "+s);
  var nums="0123456789";
  var symbols="+()<>{}_,";
  var notword=nums+symbols;
  var NUMBER=0;
  var SYMBOL=1;
  var WORD=2;
  var symbolTypes=["NUMBER","SYMBOL","WORD"];
  /** @type {BuchholzTerm} */
  var r=[];
  var startpos=scanner.pos;
  var TOP=0;
  var ANGLETERMLEFT=1;
  var ANGLETERMRIGHT=2;
  var PSITERMSUBSCRIPT=3;
  var PSITERMINNER=4;
  var PARENTHESISTERMINNER=5;
  var BRACES=6;
  var contextNames=["TOP","ANGLETERMLEFT","ANGLETERMRIGHT","PSITERMSUBSCRIPT","PSITERMINNER","PARENTHESISTERMINNER","BRACES"];
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
        appendToRSum(BUCHHOLZ_ZERO);
      }else if (num==1){
        appendToRSum(BUCHHOLZ_ONE);
      }else{
        /** @type {BuchholzPTerm[]} */
        var decomposed=[];
        for (var i=0;i<num;i++){
          state=PLUS;
          appendToRSum(BUCHHOLZ_ONE);
        }
      }
    }else if (nextWord=="ω"||nextWord=="w"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      appendToRSum(BUCHHOLZ_OMEGA);
    }else if (nextWord=="<"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var leftterm=parseBuchholz(scanner,ANGLETERMLEFT);
      var nextnext=scanner.next();
      if (nextnext!=",") throw Error("Expected a comma at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      var rightterm=parseBuchholz(scanner,ANGLETERMRIGHT);
      var nextnext=scanner.next();
      if (nextnext!=">") throw Error("Expected closing > at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      appendToRSum({left:leftterm,right:rightterm});
    }else if (nextWord=="ψ"||nextWord=="p"||nextWord=="psi"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      var nextnext=scanner.next();
      if (nextnext!="_") throw Error("Expected _ at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      var subscriptterm=parseBuchholz(scanner,PSITERMSUBSCRIPT);
      var nextnext=scanner.next();
      if (nextnext!="(") throw Error("Expected opening ( at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      var innerterm=parseBuchholz(scanner,PSITERMINNER);
      var nextnext=scanner.next();
      if (nextnext!=")") throw Error("Expected closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
      appendToRSum({left:subscriptterm,right:innerterm});
    }else if (nextWord=="("){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character "+next+" at position "+scanpos+" in expression "+scanner.s);
      if (scanner.hasNext()&&scanner.peek()!=")"){
        while (true){
          state=PLUS;
          var innerterm=parseBuchholz(scanner,PARENTHESISTERMINNER);
          appendToRSum(innerterm);
          var nextnext=scanner.next();
          if (nextnext==",") continue;
          else if (nextnext==")") break;
          else throw Error("Expected a comma or closing ) at position "+(scanner.pos-1)+", instead got "+nextnext+" in expression "+scanner.s);
        }
      }else scanner.move(1);
    }else if (nextWord=="+"){
      if (state==CLOSEDTERM){
        state=PLUS;
      }else throw Error("Unexpected character + at position "+scanpos+" in expression "+scanner.s);
    }else if (nextWord=="{"){
      if (state!=START&&state!=PLUS) throw Error("Unexpected character { at position "+scanpos+" in expression "+scanner.s);
      var subterm=parseBuchholz(scanner,BRACES);
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
      }else if (context==ANGLETERMLEFT&&peek==","){
        state=EXIT;
      }else if (context==ANGLETERMRIGHT&&peek==">"){
        state=EXIT;
      }else if (context==PSITERMSUBSCRIPT&&peek=="("){
        state=EXIT;
      }else if (context==PSITERMINNER&&peek==")"){
        state=EXIT;
      }else if (context==PARENTHESISTERMINNER&&(peek==","||peek==")")){
        state=EXIT;
      }
    }
  }
  if (context==TOP){
    if (scanner.hasNext()) throw Error("Something went wrong");
    if (state==START){}
    else if (state==PLUS) throw Error("Unexpected end of input");
    else if (state==CLOSEDTERM){}
  }else{
    if (state==START){}
    else if (state==PLUS) throw Error("Something went wrong");
    else if (state==CLOSEDTERM){}
  }
  return r;
}

/** @type {BuchholzTerm} */
var BUCHHOLZ_ZERO=[];
/** @type {BuchholzPTerm} */
var BUCHHOLZ_ONE={left:BUCHHOLZ_ZERO,right:BUCHHOLZ_ZERO};
/** @type {BuchholzPTerm} */
var BUCHHOLZ_OMEGA={left:BUCHHOLZ_ZERO,right:BUCHHOLZ_ONE};
/** @type {WeakTerm} */
var WEAK_ZERO=0;
/** @type {WeakTerm} */
var WEAK_ONE={left:WEAK_ZERO,right:WEAK_ZERO};
/** @type {WeakTerm} */
var WEAK_OMEGA={left:WEAK_ZERO,right:{left:WEAK_ONE,right:WEAK_ZERO}};

/**
 * @param {WeakTerm} x 
 * @param {WeakTerm} y 
 * @returns {WeakTerm}
 */
function oplus(x,y){
  if (x===0) return y;
  else return {left:x.left,right:oplus(x.right,y)};
}
/**
 * @param {BuchholzTerm} x 
 * @returns {WeakTerm}
 */
function triangle(x){
  if (x instanceof Array){
    if (x.length==0) return WEAK_ZERO;
    else if (x.length==2) return {left:diamond(x[0]),right:triangle(x[1])};
    else return {left:diamond(x[0]),right:triangle(x.slice(1))};
  }else return {left:diamond(x),right:WEAK_ZERO};
}
/**
 * @param {BuchholzTerm} x 
 * @returns {WeakTerm}
 */
function diamond(x){
  if (x instanceof Array){
    if (x.length==0) return WEAK_ZERO;
    else if (x.length==2) return oplus(diamond(x[0]),diamond(x[1]));
    else return oplus(diamond(x[0]),diamond(x.slice(1)));
  }else return {left:triangle(x.left),right:triangle(x.right)};
}
/**
 * @param {BuchholzTerm} x 
 * @returns {WeakTerm}
 */
function trans(x){
  if (x instanceof Array){
    if (x.length==0) return WEAK_ZERO;
    else if (x.length==2) return oplus(trans(x[0]),trans(x[1]));
    else return oplus(trans(x[0]),trans(x.slice(1)));
  }else if (x.left instanceof Array&&x.left.length==0) return diamond(x);
  else return triangle(x);
}

/**
 * @param {WeakTerm} x 
 * @param {WeakTerm} y 
 * @returns {boolean}
 */
function weakEqual(x,y){
  if (x===0) return y===0;
  else if (y===0) return false;
  else return weakEqual(x.left,y.left)&&weakEqual(x.right,y.right);
}
/**
 * @param {WeakTerm} x 
 * @param {object} options 
 * @returns {string}
 */
function stringifyWeak(x,options){
  if (x===0) return "0";
  else if (options.abbreviate){
    if ((options.abbreviate===true||options.abbreviate["1"])&&weakEqual(x,WEAK_ONE)) return "1";
    else if ((options.abbreviate===true||options.abbreviate["ω"])&&weakEqual(x,WEAK_OMEGA)) return "ω";
  }
  var left;
  if (options.abbreviate){
    if ((options.abbreviate===true||options.abbreviate["1l"])&&weakEqual(x.left,WEAK_ONE)) left="1";
    else if ((options.abbreviate===true||options.abbreviate["ωl"])&&weakEqual(x.left,WEAK_OMEGA)) left="ω";
  }
  left||=stringifyWeak(x.left,options);
  var right=stringifyWeak(x.right,options);
  return options.psi?"ψ_"+left+"("+right+")":"("+left+","+right+")";
}

var input="";
var options={
  abbreviate:undefined,
  psi:undefined
}
var optionList=[
  "abbreviate",
  "psi"
];
var abbreviateOptionList=[
  "1",
  "ω",
  "1l",
  "ωl"
];
function toggleOptions(){
  document.getElementById("options").style.display=document.getElementById("options").style.display=="none"?"block":"none";
}
var last=null;
function convertall(recalculate){
  var inputChanged=false;
  var oldinput=input;
  inputChanged||=input!=document.getElementById("input").value;
  input=document.getElementById("input").value;
  inputChanged||=!!options.abbreviate!=document.getElementById("abbreviate").checked;
  options.abbreviate=document.getElementById("abbreviate").checked&&(options.abbreviate||{});
  inputChanged||=options.detail!=document.getElementById("psi").checked;
  options.psi=document.getElementById("psi").checked;
  if (options.abbreviate){
    abbreviateOptionList.forEach(function(option){
      var elem=document.getElementById("abbreviate"+option);
      inputChanged||=options.abbreviate[option]!=elem.checked;
      options.abbreviate[option]=elem.checked;
    });
  }
  if (!recalculate&&!inputChanged) return;
  if (oldinput!=input) last=[];
  var output="";
  var lines=input.split(lineBreakRegex);
  for (var l=0;l<lines.length;l++){
    var result;
    if (oldinput!=input){
      try{
        result=trans(parseBuchholz(lines[l]));
      }catch(e){
        result=e;
        console.error(e);
      }
      last[l]=result;
    }else result=last[l];
    if (result instanceof Error){
      output+=result.stack?result.stack:result;
    }else{
      output+=stringifyWeak(result,options);
    }
    output+="\n";
  }
  document.getElementById("output").value=output;
}
var handlekey=function(e){
  setTimeout(convertall,0);
}