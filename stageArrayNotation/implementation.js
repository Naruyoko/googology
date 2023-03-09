var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ]/g;
window.onload=function (){
  console.clear();
  setupTestTerms();
  document.getElementById('input').onkeydown=handlekey;
  document.getElementById('input').onfocus=handlekey;
  document.getElementById('input').onmousedown=handlekey;
}

/**
 * Inner representation of the notation:
 * 
 * To represent elements of P:
 * Nonnegative integer n -> {label:n,inner:[]}.
 * n(α) for nonnegative integer n and α in S -> {label:n,inner:α}.
 * 
 * The elements of S are nonempty arrays of P with α+β+...+γ -> [α,β,...γ]. Valid representations should not be an empty array. Note that elements of P are no longer elements of S, so checks on array length is used for seperation and we never mix P and S.
 * 
 * @typedef {{label:number,inner:STerm}} PTerm
 * @typedef {PTerm[]} STerm
 */

/**
 * @param {string} s
 * @returns {STerm}
 */
function parseNotation(s){
  var nums="0123456789";
  /** @type {STerm[]} */
  var nestedTerms=[[]];
  var nests=0;
  var anticipateSubterm=true;
  for (var i=0;i<s.length;i++){
    if (nums.indexOf(s[i])!=-1){
      if (!anticipateSubterm) throw Error("Unexpected number at position "+i);
      var j=i+1;
      while (j<s.length&&nums.indexOf(s[j])!=-1) j++;
      var label=parseInt(s.substring(i,j));
      if (j==s.length||s[j]!="("){
        nestedTerms[nests].push({label:label,inner:[]});
        anticipateSubterm=false;
        i=j-1;
      }else{
        nestedTerms.push([]);
        nestedTerms[nests].push({label:label,inner:nestedTerms[++nests]});
        anticipateSubterm=true;
        i=j;
      }
    }else if (s[i]=="+"){
      if (anticipateSubterm) throw Error("Unexpected plus sign at position "+i);
      anticipateSubterm=true;
    }else if (s[i]==")"){
      if (anticipateSubterm) throw Error("Unexpected close parenthesis at position "+i);
      if (nests==0) throw Error("Unmatched close parenthesis at position "+i)
      nestedTerms.pop();
      nests--;
      anticipateSubterm=false;
    }else throw Error("Unexpected character "+s[i]+" at position "+i);
  }
  if (nests!=0) throw Error("Unmatched open parentheses at position "+i);
  var r=nestedTerms[0];
  if (r.length==0) throw Error("Empty input");
  return r;
}
/**
 * @param {STerm} alpha
 * @returns {string}
 */
function stringifyNotation(alpha){
  return alpha.map(function(e){return e.inner.length==0?e.label+"":e.label+"("+stringifyNotation(e.inner)+")";}).join("+");
}

/**
 * @typedef {STerm[]} NestingTrace
 */

/**
 * @param {STerm} alpha
 * @returns {NestingTrace}
 */
function nestingTrace(alpha){
  /** @type {NestingTrace} */
  var r=[];
  while (alpha.length!=0){
    r.push(alpha);
    alpha=alpha[alpha.length-1].inner;
  }
  return r;
}
/**
 * @param {STerm} alpha
 * @param {STerm} k
 * @returns {STerm}
 */
function replaceLastS(alpha,k){
  return alpha.slice(0,-1).concat(k);
}
/**
 * @param {STerm} alpha
 * @param {STerm} k
 * @returns {STerm}
 */
function replaceLastP(alpha,k){
  return alpha.slice(0,-1).concat([{label:alpha[alpha.length-1].label,inner:k}]);
}
/**
 * @param {STerm[]} trace
 * @param {STerm} k
 * @returns {STerm}
 */
function fromNestingTrace(trace,k){
  k=replaceLastS(trace[trace.length-1],k);
  for (var i=trace.length-2;i>=0;i--) k=replaceLastP(trace[i],k);
  return k;
}
/**
 * @param {NestingTrace} trace
 * @param {STerm} k
 * @param {number} n
 * @returns {STerm}
 */
function repeatNestingTrace(trace,k,n){
  for (var i=0;i<n;i++) k=fromNestingTrace(trace,k);
  return k;
}
/**
 * @param {NestingTrace} trace
 * @param {STerm} k
 * @returns {NestingTrace}
 */
function replaceInnermostTraceWithAppendable(trace,k){
  return trace.slice(0,-1).concat([replaceLastS(trace[trace.length-1],k),[]]);
}

/**
 * @param {PTerm} alpha
 * @returns {boolean}
 */
function inPasPTerm(alpha){
  return !(alpha.label==0&&alpha.inner.length==0);
}

/**
 * Boxed values and OOP go brrr
 * @typedef {[number]} InSState
 */
/**
 * @returns {InSState}
 */
function newInSState(){
  return [0];
}
/**
 * @param {number} n
 * @param {NestingTrace} trace
 * @param {InSState=} state
 * @returns {boolean} If we replace the last summed term in the trace with "k", is it in S_n?
 */
function nestingTraceInS(n,trace,state){
  for (var i=trace.length-1-(state?state[0]:0);i>=0;i--) if (trace[i][trace[i].length-1].label<n) return false;
  if (state) state[0]=trace.length;
  return true;
}
/**
 * @param {STerm} alpha
 * @param {number} n
 * @returns {STerm}
 */
function fund(alpha,n){
  if (alpha.length==1&&alpha[0].inner.length==0) return [{label:0,inner:[]}];
  if (alpha.length>1&&alpha[alpha.length-1].label==0&&alpha[alpha.length-1].inner.length==0) return alpha.slice(0,-1);
  if (alpha.length>1&&inPasPTerm(alpha[alpha.length-1])) return alpha.slice(0,-1).concat(fund([alpha[alpha.length-1]],n));
  var alphaTrace=nestingTrace(alpha);
  var b=alphaTrace[alphaTrace.length-1][alphaTrace[alphaTrace.length-1].length-1].label;
  if (alpha.length==1&&alpha[0].label!=0&&b!=0&&alpha[0].label>=b)
    // return fromNestingTrace([[{label:0,inner:[]}]].concat(alphaTrace.slice(1)),[{label:b,inner:[]}]);
    return [{label:0,inner:alpha[0].inner}];
  if (alphaTrace.length>1&&alphaTrace[alphaTrace.length-1].length==1&&alphaTrace[alphaTrace.length-1][0].label==0)
    return fromNestingTrace(alphaTrace.slice(0,-1),Array(n).fill({label:alphaTrace[alphaTrace.length-2][alphaTrace[alphaTrace.length-2].length-1].label,inner:[]}));
  if (alphaTrace.length>1&&alphaTrace[alphaTrace.length-1].length>1&&alphaTrace[alphaTrace.length-1][alphaTrace[alphaTrace.length-1].length-1].label==0)
    return fromNestingTrace(alphaTrace.slice(0,-1),Array(n).fill({label:alphaTrace[alphaTrace.length-2][alphaTrace[alphaTrace.length-2].length-1].label,inner:alphaTrace[alphaTrace.length-1].slice(0,-1)}));
  var betaTrace;
  if (alphaTrace.length>1&&alpha.length==1&&alpha[0].label<b&&b!=0&&nestingTraceInS(b,betaTrace=alphaTrace.slice(1)))
    return [{label:alpha[0].label,inner:repeatNestingTrace(replaceInnermostTraceWithAppendable(betaTrace,[{label:b-1,inner:[]}]),[],n)}];
  if (alphaTrace.length>1&&b!=0){
    for (var gammaStart=alphaTrace.length-1,state=newInSState();gammaStart>=1;gammaStart--)
      if (alphaTrace[gammaStart-1][alphaTrace[gammaStart-1].length-1].label<b&&nestingTraceInS(b,alphaTrace.slice(gammaStart),state))
        return fromNestingTrace(alphaTrace.slice(0,gammaStart),fund([alphaTrace[gammaStart-1][alphaTrace[gammaStart-1].length-1]],n));
  }
  throw Error("No rule to compute f("+stringifyNotation(alpha)+","+n+")");
}

/**
 * @param {STerm} alpha
 * @param {number} n
 * @returns {number}
 */
function largeNumberNotation(alpha,n){
  if (alpha.length==1&&alpha[0].label==0&&alpha[0].inner.length==0) return n*2;
  else return largeNumberNotation(fund(alpha,n),n*2);
}

/** @type {[string,number][]} */
var testTermsPre=[
  ["0",3],
  ["0+0",3],
  ["0(0)",3],
  ["0(0)+0",3],
  ["0(0)+0(0)",3],
  ["0(0+0)",3],
  ["0(0(0))",3],
  ["0(1)",3],
  ["0(1)+0(1)",3],
  ["0(1+0)",3],
  ["0(1+0(1))",3],
  ["0(1+1)",3],
  ["0(1(0))",3],
  ["0(1(0+0))",3],
  ["0(1(0(0)))",3],
  ["0(1(0(1)))",3],
  ["0(1(1))",3],
  ["0(1(1(0)))",3],
  ["0(1(1(1)))",3],
  ["0(2)",3],
  ["0(2)+0(2)",3],
  ["0(2+0)",3],
  ["0(2+0(2))",3],
  ["0(2+1)",3],
  ["0(2+1(2))",3],
  ["0(2+2)",3],
  ["0(2(0))",3],
  ["0(2(0(2)))",3],
  ["0(2(1))",3],
  ["0(2(1(2)))",3],
  ["0(2(2))",3],
  ["0(3)",3],
  ["1",3],
  ["1+0",3],
  ["1+1",3],
  ["1(1)",3]
];
/** @type {string[]}} */
var testTerms;
function setupTestTerms(){
  document.getElementById('input').value=testTermsPre.filter(function (t){return t[1]>=0;}).map(function(t){return "fund "+t[0]+" "+t[1];}).join("\n");
  testTerms=testTermsPre.map(function (t){return t[0];});
}

var input="";
var options={
  detail:undefined
}
var optionList=[
  "detail"
];
var last=null;
function compute(){
  var inputChanged=false;
  var oldinput=input;
  inputChanged||=input!=document.getElementById("input").value;
  input=document.getElementById("input").value;
  inputChanged||=options.detail!=document.getElementById("detail").checked;
  options.detail=document.getElementById("detail").checked;
  if (!inputChanged) return;
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
      console.time(line);
      try{
        if (cmd=="fund"||cmd=="expand"){
          var t=parseNotation(args[0]);
          result=[t];
          for (var i=1;i<args.length;i++){
            result.push(t=fund(t,+args[i]));
          }
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
    }else if (cmd=="fund"||cmd=="expand"){
      if (options.detail){
        for (var i=1;i<result.length;i++){
          output+="f("+stringifyNotation(result[i-1])+","+args[i]+")="+stringifyNotation(result[i])+(i==result.length-1?"":"\n");
        }
      }else{
        output+=stringifyNotation(result[result.length-1]);
      }
    }else{
      output+="Unknown command "+cmd;
    }
    output+="\n\n";
  }
  document.getElementById("output").value=output;
}
var handlekey=function(e){}