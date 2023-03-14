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
 * 0 -> [].
 * 
 * The elements of P are (α,β) -> [α,β].
 * 
 * The elements of S are nonempty arrays of P with α+β+...+γ -> [α,β,...γ]. Valid representations should not be an empty array. Note that elements of P are no longer elements of S, so checks on array length is used for seperation and we never mix P and S.
 * 
 * @typedef {[STerm,STerm]} PTerm
 * @typedef {PTerm[]} STerm
 */

/** @type {STerm} */
var ZERO_S=[];
/** @type {PTerm} */
var ONE_P=[ZERO_S,ZERO_S];
/**
 * @param {STerm} alpha
 * @returns {boolean}
 */
function isZeroS(alpha){
  return alpha.length==0;
}
/**
 * @param {PTerm} alpha
 * @returns {boolean}
 */
function isOneP(alpha){
  return isZeroS(alpha[0])&&isZeroS(alpha[1]);
}
/**
 * @param {string} s
 * @returns {STerm}
 */
function parseNotation(s){
  var nums="0123456789";
  /** @type {STerm[]} */
  var nestedTerms=[null];
  var nests=0;
  var anticipateSubterm=true;
  for (var i=0;i<s.length;i++){
    if (nums.indexOf(s[i])!=-1){
      if (!anticipateSubterm) throw Error("Unexpected number at position "+i);
      var j=i+1;
      while (j<s.length&&nums.indexOf(s[j])!=-1) j++;
      var n=parseInt(s.substring(i,j));
      if (n===0){
        if (nestedTerms[nests]!==null) throw Error("0 is not allowed in a sum at position "+i);
        nestedTerms[nests]=ZERO_S;
      }else{
        if (nestedTerms[nests]===null) nestedTerms[nests]=[];
        while (n--) nestedTerms[nests].push(ONE_P);
      }
      anticipateSubterm=false;
      i=j-1;
    }else if (s[i]=="+"){
      if (anticipateSubterm) throw Error("Unexpected plus sign at position "+i);
      if (nestedTerms[nests].length==0) throw Error("0 is not allowed in a sum at position "+i);
      anticipateSubterm=true;
    }else if (s[i]=="("){
      if (!anticipateSubterm) throw Error("Unexpected open parenthesis at position "+i);
      if (nestedTerms[nests]===null) nestedTerms[nests]=[];
      nestedTerms[nests].push([null,null]);
      nestedTerms.push(null);
      nests++;
      anticipateSubterm=true;
    }else if (s[i]==","){
      if (anticipateSubterm||nests==0) throw Error("Unexpected comma at position "+i);
      if (nestedTerms[nests-1][nestedTerms[nests-1].length-1][1]!==null) throw Error("Unexpected comma at position "+i);
      nestedTerms[nests-1][nestedTerms[nests-1].length-1][0]=nestedTerms[nests];
      nestedTerms[nests]=null;
      anticipateSubterm=true;
    }else if (s[i]==")"){
      if (anticipateSubterm) throw Error("Unexpected close parenthesis at position "+i);
      if (nests==0) throw Error("Unmatched close parenthesis at position "+i);
      nestedTerms[nests-1][nestedTerms[nests-1].length-1][1]=nestedTerms[nests];
      nestedTerms.pop();
      nests--;
      anticipateSubterm=false;
    }else throw Error("Unexpected character "+s[i]+" at position "+i);
  }
  if (nests!=0) throw Error("Unmatched open parentheses at position "+i);
  if (anticipateSubterm) throw Error("Unexpected end of input");
  var r=nestedTerms[0];
  if (r===null) throw Error("Empty input");
  return r;
}
/**
 * @param {STerm} alpha
 * @param {boolean|object} abbreviate
 * @returns {string}
 */
function stringifyNotation(alpha,abbreviate){
  if (alpha.length==0) return "0";
  else{
    var s="";
    for (var i=0;i<alpha.length;i++){
      if (s) s+="+";
      if (abbreviate&&(abbreviate===true||abbreviate["1"])&&isOneP(alpha[i])){
        if (abbreviate===true||abbreviate["n"]){
          for (var j=i+1;j<alpha.length&&isOneP(alpha[j]);j++);
          s+=j-i;
          i=j;
        }else s+="1";
      }else s+="("+stringifyNotation(alpha[i][0],abbreviate)+","+stringifyNotation(alpha[i][1],abbreviate)+")";
    }
    return s;
  }
}
/**
 * @param {STerm} alpha
 * @param {STerm} beta
 * @returns {boolean}
 */
function equal(alpha,beta){
  return alpha.length==beta.length&&alpha.every(function(e,i){return equal(e[0],beta[i][0])&&equal(e[1],beta[i][1]);});
}

/**
 * @param {STerm} alpha
 * @returns {boolean}
 */
 function inP(alpha){
  return alpha.length==1;
}
/**
 * @param {STerm} alpha
 * @returns {boolean}
 */
function inD(alpha){
  return alpha.length>0&&isOneP(alpha[alpha.length-1]);
}
/**
 * @param {STerm} alpha
 * @returns {STerm}
 */
function pred(alpha){
  return alpha.slice(0,-1);
}
/**
 * @param {STerm} alpha
 * @returns {STerm}
 */
function succ(alpha){
  return alpha.concat([ONE_P]);
}
/**
 * @param {STerm} alpha
 * @param {STerm} beta
 * @returns {boolean}
 */
function lessThan(alpha,beta){
  if (isZeroS(alpha)) return !isZeroS(beta);
  if (isZeroS(beta)) return false;
  if (inP(alpha)){
    if (inP(beta)) return lessThan(alpha[0][0],beta[0][0])||equal(alpha[0][0],beta[0][0])&&lessThan(alpha[0][1],beta[0][1]);
    else return lessThan(alpha,[beta[0]])||equal(alpha,[beta[0]]);
  }else{
    if (inP(beta)) return lessThan([alpha[0]],beta);
    else return lessThan([alpha[0]],[beta[0]])||equal([alpha[0]],[beta[0]])&&lessThan(alpha.slice(1),beta.slice(1));
  }
}

/**
 * @typedef {[STerm,0|1][]} NestingTrace
 */
/**
 * @param {STerm} alpha
 * @returns {PTerm}
 */
 function lastSummedTerm(alpha){
  return alpha[alpha.length-1];
}
/**
 * @param {STerm} alpha
 * @returns {NestingTrace}
 */
function nestingTrace(alpha){
  /** @type {NestingTrace} */
  var r=[];
  while (!isZeroS(alpha)){
    var into;
    r.push([alpha,into=isZeroS(alpha[alpha.length-1][1])?0:1]);
    alpha=alpha[alpha.length-1][into];
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
 * @param {0|1} into
 * @param {STerm} k
 * @returns {STerm}
 */
function replaceLastP(alpha,into,k){
  return alpha.slice(0,-1).concat([into?[alpha[alpha.length-1][0],k]:[k,alpha[alpha.length-1][1]]]);
}
/**
 * @param {NestingTrace} trace
 * @param {STerm} k
 * @returns {STerm}
 */
function fromNestingTrace(trace,k){
  for (var i=trace.length-1;i>=0;i--) k=replaceLastP(trace[i][0],trace[i][1],k);
  return k;
}
/**
 * @param {NestingTrace} trace
 * @param {STerm} k
 * @returns {STerm}
 */
function fromNestingTraceAppend(trace,k){
  k=replaceLastS(trace[trace.length-1][0],k);
  for (var i=trace.length-2;i>=0;i--) k=replaceLastP(trace[i][0],trace[i][1],k);
  return k;
}
/**
 * @param {NestingTrace} trace
 * @param {STerm} k
 * @param {number} n
 * @returns {STerm}
 */
function repeatNestingTrace(trace,k,n){
  for (var i=0;i<n;i++) k=fromNestingTraceAppend(trace,k);
  return k;
}
/**
 * @param {NestingTrace} trace
 * @param {STerm} k
 * @param {0|1} into
 * @returns {NestingTrace}
 */
function replaceInnermostTraceWithAppendable(trace,k,into){
  return trace.slice(0,-1).concat([[replaceLastS(trace[trace.length-1][0],k),into],[[],0]]);
}

/**
 * Boxed values and OOP go brrr
 * @typedef {[number]} NumberSlot
 */
/**
 * @returns {NumberSlot}
 */
function newNumberSlot(){
  return [0];
}
/**
 * @param {STerm} alpha
 * @param {NestingTrace} trace
 * @param {NumberSlot=} slot
 * @returns {boolean} If we replace the last summed term in the second-to-last trace with "k", is it in TB_α?
 */
function nestingTraceInTB(alpha,trace,slot){
  if (slot&&slot[0]==-1) return false;
  for (var i=trace.length-2-(slot?slot[0]:0);i>=0;i--){
    var principalWithBeta=lastSummedTerm(trace[i][0]);
    if (!isZeroS(principalWithBeta[1])&&lessThan(principalWithBeta[0],alpha)){
      if (slot) slot[0]=-1;
      return false;
    }
  }
  if (slot) slot[0]=trace.length-1;
  return true;
}
/**
 * @param {STerm} alpha
 * @param {STerm} fromBeta Assumption: fromBeta=TB_{α,β}((α,0))∈TB_α
 * @param {NestingTrace} trace
 * @param {NumberSlot=} slot1
 * @param {NumberSlot=} slot2
 * @returns {boolean} If we replace the last summed term in the second-to-last trace with "k", is it in RB_α?
 */
function nestingTraceInRB(alpha,fromBeta,trace,slot1,slot2){
  if (slot2&&slot2[0]==-1) return false;
  slot1||=newNumberSlot();
  if (slot1[0]>=0)
    for (var i=trace.length-2-slot1[0];i>=0;i--)
      if (!nestingTraceInTB(alpha,trace.slice(i),slot1)){
        slot1[0]=i-trace.length+1;
        break;
      }
  if (slot1[0]>=0||trace.length-1+slot1[0]<=0) return true;
  slot2||=newNumberSlot();
  for (var i=trace.length-1+slot1[0]-slot2[0];i>=0;i--)
    if (!nestingTraceInTB(alpha,trace.slice(i,trace.length+slot1[0]),slot2)){
      if (lessThan(fromBeta,fromNestingTraceAppend(trace.slice(i+1,trace.length+slot1[0]),[[succ(lastSummedTerm(trace[trace.length-1+slot1[0]][0])[0]),ZERO_S]]))){
        slot1[0]=i-trace.length+1;
        slot2[0]=0;
      }else{
        slot2[0]=-1;
        return false;
      }
    }
  return lessThan(fromBeta,fromNestingTraceAppend(trace.slice(0,trace.length+slot1[0]),[[succ(lastSummedTerm(trace[trace.length-1+slot1[0]][0])[0]),ZERO_S]]));
}
/**
 * @param {STerm} alpha
 * @param {number} n
 * @returns {STerm}
 */
function fund(alpha,n){
  if (isZeroS(alpha)||alpha.length==1&&isZeroS(alpha[0][1])) return ZERO_S;
  if (alpha.length>1&&isZeroS(alpha[alpha.length-1][1])) return alpha.slice(0,-1);
  if (alpha.length>1) return alpha.slice(0,-1).concat(fund([alpha[alpha.length-1]],n));
  var alphaTrace=nestingTrace(alpha);
  if (!isZeroS(alpha[0][0])) return [[ZERO_S,alpha[0][1]]];
  for (var gammaPos=alphaTrace.length-1;gammaPos>=0;gammaPos--){
    var principalWithGamma=lastSummedTerm(alphaTrace[gammaPos][0]);
    if (inD(principalWithGamma[1])) return fromNestingTraceAppend(alphaTrace.slice(0,gammaPos+1),Array(n).fill([principalWithGamma[0],pred(principalWithGamma[1])]));
  }
  for (var deltaPos=alphaTrace.length-1;deltaPos>=1;deltaPos--){
    var principalWithDelta=lastSummedTerm(alphaTrace[deltaPos][0]);
    if (inD(principalWithDelta[0])&&isZeroS(principalWithDelta[1]))
      for (var bPos=deltaPos-1,slotTBB=newNumberSlot();bPos>=0&&slotTBB[0]!=-1;bPos--){
        var principalWithB=lastSummedTerm(alphaTrace[bPos][0]);
        var betaTrace;
        if (!isZeroS(principalWithB[1])&&lessThan(principalWithB[0],principalWithDelta[0])&&nestingTraceInTB(principalWithDelta[0],betaTrace=alphaTrace.slice(bPos+1,deltaPos+1),slotTBB)){
          var gammaTrace;
          if (nestingTraceInRB(principalWithDelta[0],principalWithB[1],gammaTrace=alphaTrace.slice(1,deltaPos+1)))
            return [[ZERO_S,repeatNestingTrace(replaceInnermostTraceWithAppendable(gammaTrace,[[pred(principalWithDelta[0]),ZERO_S]],1),[],n)]];
          for (var iotaPos=deltaPos-1,slotRB1=newNumberSlot(),slotRB2=newNumberSlot();iotaPos>=1&&slotRB2[0]!=-1;iotaPos--){
            var principalWithPredIota=lastSummedTerm(alphaTrace[iotaPos][0]);
            if (lessThan(principalWithPredIota[0],principalWithDelta[0])&&nestingTraceInRB(principalWithDelta[0],principalWithB[1],gammaTrace=alphaTrace.slice(iotaPos+1,deltaPos+1),slotRB1,slotRB2))
              for (var zetaPos=iotaPos-1,slotTBZeta=newNumberSlot();zetaPos>=0&&slotTBZeta[0]!=-1;zetaPos--){
                var principalWithZeta=lastSummedTerm(alphaTrace[zetaPos][0]);
                if (lessThan(principalWithZeta[0],principalWithDelta[0])&&nestingTraceInTB(principalWithDelta[0],alphaTrace.slice(zetaPos+1,iotaPos+1),slotTBZeta)&&!lessThan(principalWithB[1],fromNestingTraceAppend(alphaTrace.slice(zetaPos+1,iotaPos+1),[[succ(principalWithPredIota[0]),ZERO_S]])))
                  return fromNestingTrace(alphaTrace.slice(0,iotaPos+1),repeatNestingTrace(replaceInnermostTraceWithAppendable(gammaTrace,[[pred(principalWithDelta[0]),ZERO_S]],1),[],n));
              }
          }
        }
      }
  }
  throw Error("No rule to compute f("+stringifyNotation(alpha)+","+n+")");
}

/**
 * @param {STerm} alpha
 * @param {number} n
 * @returns {number}
 */
function largeNumberNotation(alpha,n){
  if (isZeroS(alpha)) return n*2;
  else return largeNumberNotation(fund(alpha,n),n*2);
}
/**
 * @param {number} n
 * @returns {STerm}
 */
function limitNotation_aux(n){
  return [[n<=1?ZERO_S:limitNotation_aux(n-1),ZERO_S]];
}
/**
 * @param {number} n
 * @returns {STerm}
 */
function limitNotation(n){
  return [[ZERO_S,limitNotation_aux(n)]];
}
/**
 * @param {number} n 
 * @returns {number}
 */
function largeFunction(n){
  return largeNumberNotation(limitNotation(n),n);
}
function calculateN(){
  var r=100;
  for (var i=0;i<100;i++) r=largeFunction(r);
  return r;
}
/**
 * 
 * @param {STerm} x
 * @param {number} limit
 * @returns {{isStandard:boolean,path:STerm[],funds:number[]}}
 */
function findOTPath(x,limit){
  if (typeof limit=="undefined"||limit==-1) limit=Infinity;
  if (isZeroS(x)){
    return {isStandard:true,path:[x],funds:[-1]};
  }else{
    var n=1;
    var t;
    while(n<=limit&&!(equal(x,t=limitNotation(n))||lessThan(x,t))){
      n++;
    };
    if (n>limit) return {isStandard:false,path:[],funds:[]};
    t=limitNotation(n);
    var r={isStandard:false,path:[t],funds:[n]};
    while (!equal(x,t)){
      n=1;
      var nt;
      while (n<=limit&&lessThan(nt=fund(t,n),x)) n++;
      if (n>limit) return r;
      r.path.push(t=nt);
      r.funds.push(n);
    }
    r.isStandard=true;
    return r;
  }
}
/**
 * @param {STerm} x
 * @param {number} limit
 * @returns {boolean}
 */
function isStandard(x,limit){
  return findOTPath(x,limit).isStandard;
}

/** @type {[string,number][]} */
var testTermsPre=[
  ["0",3],
  ["1",3],
  ["2",3],
  ["(0,1)",3],
  ["(0,1)+1",3],
  ["(0,1)+(0,1)",3],
  ["(0,2)",3],
  ["(0,(0,1))",3],
  ["(0,(1,0))",3],
  ["(0,(1,0))+(0,(1,0))",3],
  ["(0,(1,0)+1)",3],
  ["(0,(1,0)+(0,(0,(1,0))))",3],
  ["(0,(1,0)+(0,(0,(1,0))+1))",-1],
  ["(0,(1,0)+(0,(0,(1,0))+(0,(1,0))))",3],
  ["(0,(1,0)+(0,(0,(1,0)+1)))",-1],
  ["(0,(1,0)+(0,(0,(1,0)+(0,(0,(1,0))))))",3],
  ["(0,(1,0)+(0,(1,0)))",3],
  ["(0,(1,0)+(0,(1,0))+(0,(0,(1,0))))",3],
  ["(0,(1,0)+(0,(1,0))+(0,(0,(1,0)+(0,(1,0)))))",3],
  ["(0,(1,0)+(0,(1,0))+(0,(1,0)))",3],
  ["(0,(1,0)+(0,(1,0)+1))",-1],
  ["(0,(1,0)+(0,(1,0)+(0,(0,(1,0)))))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(0,(1,0)+(0,(1,0))))))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0))))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0)))+(0,(1,0)))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0)))+(0,(1,0)+(0,(1,0))))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0))+1))",-1],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0))+(0,(1,0))))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0)+1))+(0,(1,0)))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0)+1))+(0,(1,0)+(0,(1,0))))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0)+1))+(0,(1,0)+(0,(1,0)+1)))",-1],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0)+1)+1))",-1],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0)+1)+(0,(1,0))))",3],
  ["(0,(1,0)+(0,(1,0)+(0,(1,0)+(0,(1,0)))))",3],
  ["(0,(1,0)+(1,0))",3],
  ["(0,(1,0)+(1,0)+(0,(0,(1,0))))",3],
  ["(0,(1,0)+(1,0)+(0,(0,(1,0)+(0,(1,0)))))",3],
  ["(0,(1,0)+(1,0)+(0,(0,(1,0)+(1,0))))",3],
  ["(0,(1,0)+(1,0)+(0,(1,0)))",3],
  ["(0,(1,0)+(1,0)+(0,(1,0)+(0,(1,0))))",3],
  ["(0,(1,0)+(1,0)+(0,(1,0)+(0,(1,0)+(1,0))))",3],
  ["(0,(1,0)+(1,0)+(0,(1,0)+(1,0)))",3],
  ["(0,(1,0)+(1,0)+(1,0))",3],
  ["(0,(1,1))",3],
  ["(0,(1,1)+(0,(1,0)))",3],
  ["(0,(1,1)+(0,(1,1)))",3],
  ["(0,(1,1)+(0,(1,1)+(0,(1,0))))",3],
  ["(0,(1,1)+(0,(1,1)+(0,(1,1))))",3],
  ["(0,(1,1)+(1,0))",3],
  ["(0,(1,1)+(1,0)+(0,(1,1)+(0,(1,1)+(1,0))))",3],
  ["(0,(1,1)+(1,0)+(0,(1,1)+(1,0)))",3],
  ["(0,(1,1)+(1,0)+(1,0))",3],
  ["(0,(1,1)+(1,1))",-1],
  ["(0,(1,2))",3],
  ["(0,(1,(0,1)))",3],
  ["(0,(1,(0,(0,(1,0)))))",3],
  ["(0,(1,(0,(1,0))))",3],
  ["(0,(1,(0,(1,0)+(0,(1,0)))))",3],
  ["(0,(1,(0,(1,0)+(0,(1,0)+(1,0)))))",3],
  ["(0,(1,(0,(1,0)+(0,(1,1)))))",3],
  ["(0,(1,(0,(1,0)+(1,0))))",3],
  ["(0,(1,(0,(1,1))))",3],
  ["(0,(1,(0,(1,(0,(1,0))))))",3],
  ["(0,(1,(1,0)))",3],
  ["(0,(1,(1,0))+(0,(1,0)))",3],
  ["(0,(1,(1,0))+(0,(1,(0,(1,(1,0))))))",3],
  ["(0,(1,(1,0))+(0,(1,(0,(1,(1,0))))+(1,0)))",3],
  ["(0,(1,(1,0))+(0,(1,(0,(1,(1,0))))+(1,(0,(1,(1,0))))))",3],
  ["(0,(1,(1,0))+(0,(1,(0,(1,(1,0)))+(0,(1,0)))))",3],
  ["(0,(1,(1,0))+(0,(1,(0,(1,(1,0)))+(0,(1,(1,0))))))",3],
  ["(0,(1,(1,0))+(0,(1,(0,(1,(1,0))+1))))",-1],
  ["(0,(1,(1,0))+(0,(1,(0,(1,(1,0))+(0,(1,(0,(1,(1,0)))))))))",3],
  ["(0,(1,(1,0))+(0,(1,(1,0))))",3],
  ["(0,(1,(1,0))+(0,(1,(1,0)))+(0,(1,(1,0))))",3],
  ["(0,(1,(1,0))+(0,(1,(1,0))+1))",-1],
  ["(0,(1,(1,0))+(0,(1,(1,0))+(0,(1,(0,(1,(1,0)))))))",3],
  ["(0,(1,(1,0))+(0,(1,(1,0))+(0,(1,(1,0)))))",3],
  ["(0,(1,(1,0))+(1,0))",3],
  ["(0,(1,(1,0))+(1,0)+(0,(1,(0,(1,(1,0))+(1,0)))))",3],
  ["(0,(1,(1,0))+(1,0)+(0,(1,(1,0))))",3],
  ["(0,(1,(1,0))+(1,0)+(0,(1,(1,0))+(0,(1,(1,0))+(1,0))))",3],
  ["(0,(1,(1,0))+(1,0)+(0,(1,(1,0))+(1,0)))",3],
  ["(0,(1,(1,0))+(1,0)+(1,0))",-1],
  ["(0,(1,(1,0))+(1,1))",-1],
  ["(0,(1,(1,0))+(1,(0,(1,0))))",3],
  ["(0,(1,(1,0))+(1,(0,(1,(0,(1,(1,0)))))))",-1],
  ["(0,(1,(1,0))+(1,(0,(1,(1,0)))))",3],
  ["(0,(1,(1,0))+(1,(0,(1,(1,0)))+(0,(1,(1,0)))))",3],
  ["(0,(1,(1,0))+(1,(0,(1,(1,0))+(0,(1,(1,0))))))",3],
  ["(0,(1,(1,0))+(1,(0,(1,(1,0))+(1,0))))",3],
  ["(0,(1,(1,0))+(1,(1,0)))",3],
  ["(0,(1,(1,0))+(1,(1,0))+(0,(1,(1,0))+(0,(1,(1,0))+(1,(1,0)))))",3],
  ["(0,(1,(1,0))+(1,(1,0))+(0,(1,(1,0))+(1,0)))",-1],
  ["(0,(1,(1,0))+(1,(1,0))+(0,(1,(1,0))+(1,(0,(1,(0,(1,(1,0))+(1,(1,0))))))))",3],
  ["(0,(1,(1,0))+(1,(1,0))+(0,(1,(1,0))+(1,(0,(1,(1,0))))))",3],
  ["(0,(1,(1,0))+(1,(1,0))+(0,(1,(1,0))+(1,(1,0))))",-1],
  ["(0,(1,(1,0))+(1,(1,0))+(1,0))",-1],
  ["(0,(1,(1,0))+(1,(1,0))+(1,(0,(1,(1,0))+(1,(1,0)))))",3],
  ["(0,(1,(1,0))+(1,(1,0))+(1,(1,0)))",-1],
  ["(0,(1,(1,0)+1))",-1],
  ["(0,(1,(1,0)+(0,(1,0))))",3],
  ["(0,(1,(1,0)+(1,0)))",3],
  ["(0,(1,(1,1)))",-1],
  ["(0,(1,(1,(1,0))))",3],
  ["(0,(2,0))",3],
  ["(0,(2,0))+(0,(2,0))",3],
  ["(0,(2,0)+1)",3],
  ["(0,(2,0)+(0,(1,(2,0))))",3],
  ["(0,(2,0)+(0,(1,(2,0))+(0,(2,0))))",3],
  ["(0,(2,0)+(0,(1,(2,0))+(1,0)))",3],
  ["(0,(2,0)+(0,(1,(2,0))+(1,(1,0))))",3],
  ["(0,(2,0)+(0,(1,(2,0))+(1,(2,0))))",3],
  ["(0,(2,0)+(0,(1,(2,0)+1)))",-1],
  ["(0,(2,0)+(0,(1,(2,0)+(0,(1,0)))))",-1],
  ["(0,(2,0)+(0,(2,0)))",3],
  ["(0,(2,0)+(1,0))",3],
  ["(0,(2,0)+(1,0)+(0,(2,0)+(0,(2,0)+(1,0))))",3],
  ["(0,(2,0)+(1,0)+(0,(2,0)+(1,0)))",3],
  ["(0,(2,0)+(1,0)+(1,0))",-1],
  ["(0,(2,0)+(1,1))",-1],
  ["(0,(2,0)+(1,(1,(2,0))))",3],
  ["(0,(2,0)+(1,(2,0)))",3],
  ["(0,(2,0)+(2,0))",3],
  ["(0,(2,1))",3],
  ["(0,(2,(0,(1,(2,0)))))",3],
  ["(0,(2,(0,(1,(2,0))+(0,(2,0)))))",3],
  ["(0,(2,(0,(1,(2,0))+(1,0))))",3],
  ["(0,(2,(0,(1,(2,0))+(1,(2,0)))))",3],
  ["(0,(2,(0,(2,0))))",3],
  ["(0,(2,(0,(2,0)+(0,(1,(2,0))))))",3],
  ["(0,(2,(0,(2,0)+(0,(2,0)))))",3],
  ["(0,(2,(0,(2,0)+(1,(2,0)))))",3],
  ["(0,(2,(0,(2,0)+(2,0))))",3],
  ["(0,(2,(0,(2,1))))",-1],
  ["(0,(2,(1,0)))",3],
  ["(0,(2,(1,(1,(2,0)))))",3],
  ["(0,(2,(1,(2,0))))",3],
  ["(0,(2,(2,0)))",3],
  ["(0,(3,0))",3],
  ["(0,((0,1),0))",3],
  ["(0,((0,1),0)+(0,((0,1),0)))",3],
  ["(0,((0,1),0)+(1,0))",3],
  ["(0,((0,1),0)+((0,1),0))",3],
  ["(0,((0,1),1))",3],
  ["(0,((0,1)+1,0))",3],
  ["(0,((0,1)+1,0)+(0,(1,0)))",3],
  ["(0,((0,1)+1,0)+(0,(1,((0,1)+1,0))))",3],
  ["(0,((0,1)+1,0)+(0,(2,0)))",3],
  ["(0,((0,1)+1,0)+(0,((0,1),((0,1)+1,0))))",3],
  ["(0,((0,1)+1,0)+(1,0))",-1],
  ["(0,((0,1)+1,0)+(1,(0,((0,1)+1,0))))",3],
  ["(0,((0,1)+1,0)+(1,(1,((0,1)+1,0))))",3],
  ["(0,((0,1)+1,0)+(1,(2,0)))",3],
  ["(0,((0,1)+1,0)+(1,((0,1),((0,1)+1,0))))",3],
  ["(0,((0,1)+1,0)+(2,0))",-1],
  ["(0,((0,1)+1,0)+((0,1),0))",-1],
  ["(0,((0,1)+1,0)+((0,1),(0,((0,1)+1,0))))",3],
  ["(0,((0,1)+1,0)+((0,1),((0,1),((0,1)+1,0))))",3],
  ["(0,((0,1)+1,0)+((0,1),((0,1)+1,0)))",3],
  ["(0,((0,1)+1,0)+((0,1)+1,0))",3],
  ["(0,((0,1)+1,1))",-1],
  ["(0,((0,1)+(0,1),0))",3],
  ["(0,((0,2),0))",3],
  ["(0,((0,(0,1)),0))",3],
  ["(0,((0,(0,(1,0))),0))",3],
  ["(0,((0,(0,((0,1),0))),0))",-1],
  ["(0,((0,(0,((0,1)+1,0))),0))",3],
  ["(0,((0,(1,0)),0))",3],
  ["(0,((0,(1,0)+(0,(1,0)+(1,0))),0))",3],
  ["(0,((0,(1,0)+(1,0)),0))",-1],
  ["(0,((0,(1,(1,0))),0))",-1],
  ["(0,((0,(1,(2,0))),0))",3],
  ["(0,((0,(2,0)),0))",3],
  ["(0,((0,((0,1),0)),0))",-1],
  ["(0,((1,0),0))",3],
  ["(0,((1,0),(0,((0,(1,0)),0))))",3],
  ["(0,((1,0),(0,((1,0),0))))",3],
  ["(0,((1,0),(1,0)))",3],
  ["(0,((1,0),(1,((0,(1,0)),0))))",3],
  ["(0,((1,0),(1,((1,0),0))))",3],
  ["(0,((1,0),((0,(1,0)),0)))",3],
  ["(0,((1,0),((1,0),0)))",3],
  ["(0,((1,0)+1,0))",3],
  ["(0,((1,1),0))",3],
  ["(0,((1,(0,(1,0))),0))",3],
  ["(0,((1,(0,((1,0),0))),0))",3],
  ["(0,((1,(1,0)),0))",3],
  ["(0,((2,0),0))",3],
  ["(0,((2,(0,(1,0))),0))",3],
  ["(0,((2,(0,((2,0),0))),0))",3],
  ["(0,((2,(1,0)),0))",3],
  ["(0,((2,(1,((2,0),0))),0))",3],
  ["(0,((2,(2,0)),0))",3],
  ["(0,((3,0),0))",3],
  ["(0,(((0,1),0),0))",3],
  ["(0,(((1,0),0),0))",3],
  ["(0,(((1,0),0),(0,(((1,0),0),0))))",3],
  ["(0,(((1,0),0),(1,0)))",-1],
  ["(0,(((1,0),0),((0,(((1,0),0),0)),0)))",3],
  ["(0,(((1,0),0),((1,0),0)))",-1],
  ["(0,(((1,0),0),(((0,(((1,0),0),0)),0),0)))",3],
  ["(0,(((1,0),0),(((1,0),0),0)))",-1],
  ["(0,(((1,0),0)+1,0))",3],
  ["(0,(((1,(0,(((1,0),0),0))),0),0))",-1],
  ["(0,(((1,(1,0)),0),0))",-1],
  ["(0,(((1,(2,0)),0),0))",-1],
  ["(0,(((1,((1,0),0)),0),0))",-1],
  ["(0,(((1,((2,0),0)),0),0))",-1],
  ["(0,(((1,(((1,0),0),0)),0),0))",-1],
  ["(0,(((2,0),0),0))",-1],
  ["(0,((((0,1),0),0),0))",-1],
  ["(0,((((1,0),0),0),0))",-1],
  ["(1,0)",3],
  ["(1,0)+1",3],
  ["(1,0)+(1,0)",3],
  ["(1,1)",3],
  ["(1,(1,0))",3],
  ["(1,(2,0))",3]
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
        result=lessThan(parseNotation(testTerms[i]),parseNotation(testTerms[j]));
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
  for (var i=0;i<testTerms.length&&lessThan(parseNotation(testTerms[i]),[[[ONE_P],ZERO_S]]);i++){
    if (logInfoToConsole) console.log("%cTesting: inOT, "+testTerms[i]+".","color:gold");
    var d=Date.now();
    var caught=false;
    var result;
    try{
      result=isStandard(parseNotation(testTerms[i]),10);
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
  "n"
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
          result=stringifyNotation(parseNotation(args[0]),false);
        }else if (cmd=="abbreviate"||cmd=="abbr"){
          result=null;
        }else if (cmd=="inP"){
          result=inP(parseNotation(args[0]));
        }else if (cmd=="inD"){
          result=inD(parseNotation(args[0]));
        }else if (cmd=="lessThan"||cmd=="<"){
          result=lessThan(parseNotation(args[0]),parseNotation(args[1]));
        }else if (cmd=="fund"||cmd=="expand"){
          var t=parseNotation(args[0]);
          result=[t];
          for (var i=1;i<args.length;i++){
            result.push(t=fund(t,+args[i]));
          }
        }else if (cmd=="inOT"||cmd=="isStandard"){
          result=findOTPath(parseNotation(args[0]),+args[1]||3);
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
      output+=stringifyNotation(result,options.abbreviate||true);
    }else if (cmd=="inP"){
      output+=result;
    }else if (cmd=="inD"){
      output+=result;
    }else if (cmd=="lessThan"||cmd=="<"){
      output+=result;
    }else if (cmd=="fund"||cmd=="expand"){
      if (options.detail){
        for (var i=1;i<result.length;i++){
          output+="f("+stringifyNotation(result[i-1],options.abbreviate)+","+args[i]+")="+stringifyNotation(result[i],options.abbreviate)+(i==result.length-1?"":"\n");
        }
      }else{
        output+=stringifyNotation(result[result.length-1],options.abbreviate);
      }
    }else if (cmd=="inOT"||cmd=="isStandard"){
      if (options.detail){
        for (var i=1;i<result.path.length;i++){
          output+="f("+stringifyNotation(result.path[i-1],options.abbreviate)+","+result.funds[i]+")="+stringifyNotation(result.path[i],options.abbreviate)+"\n";
        }
        if (result.isStandard) output+=stringifyNotation(parseNotation(args[0]),options.abbreviate)+"∈OT";
        else output+=stringifyNotation(parseNotation(args[0]),options.abbreviate)+"∉OT limited to n≦"+(args[1]||3);
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