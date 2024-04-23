/// <reference path="./common.js" />

var lineBreakRegex=/\r?\n/g;

window.onload=function (){
  console.clear();
  setupTestTerms();
  document.getElementById('input').onkeydown=handlekey;
  document.getElementById('input').onfocus=handlekey;
  document.getElementById('input').onmousedown=handlekey;
  requestCompute();
}


var initTerms=[
  "(0,0)",
  "(0,0)(0,0)",
  "(0,0)(1,0)",
  "(0,0)(1,0)(0,0)",
  "(0,0)(1,0)(0,0)(1,0)",
  "(0,0)(1,0)(1,0)",
  "(0,0)(1,0)(2,0)",
  "(0,0)(1,0)(2,0)(0,0)",
  "(0,0)(1,0)(2,0)(0,0)(1,0)",
  "(0,0)(1,0)(2,0)(0,0)(1,0)(2,0)",
  "(0,0)(1,0)(2,0)(1,0)",
  "(0,0)(1,0)(2,0)(1,0)(2,0)",
  "(0,0)(1,0)(2,0)(2,0)",
  "(0,0)(1,0)(2,0)(3,0)",
  "(0,0)(1,1)",
  "(0,0)(1,1)(1,0)",
  "(0,0)(1,1)(1,0)(2,0)",
  "(0,0)(1,1)(1,0)(2,1)",
  "(0,0)(1,1)(1,0)(2,1)(1,0)",
  "(0,0)(1,1)(1,0)(2,1)(1,0)(2,0)",
  "(0,0)(1,1)(1,0)(2,1)(1,0)(2,1)",
  "(0,0)(1,1)(1,0)(2,1)(2,0)",
  "(0,0)(1,1)(1,0)(2,1)(2,0)(3,0)",
  "(0,0)(1,1)(1,0)(2,1)(2,0)(3,1)",
  "(0,0)(1,1)(1,1)",
  "(0,0)(1,1)(2,0)",
  "(0,0)(1,1)(2,0)(1,0)(2,1)(3,0)",
  "(0,0)(1,1)(2,0)(1,1)",
  "(0,0)(1,1)(2,0)(1,1)(2,0)",
  "(0,0)(1,1)(2,0)(2,0)",
  "(0,0)(1,1)(2,0)(3,0)",
  "(0,0)(1,1)(2,0)(3,1)",
  "(0,0)(1,1)(2,0)(3,1)(4,0)",
  "(0,0)(1,1)(2,1)",
  "(0,0)(1,1)(2,1)(1,1)",
  "(0,0)(1,1)(2,1)(2,0)",
  "(0,0)(1,1)(2,1)(2,1)",
  "(0,0)(1,1)(2,1)(3,0)",
  "(0,0)(1,1)(2,1)(3,0)(4,1)(5,1)",
  "(0,0)(1,1)(2,1)(3,1)",
  "(0,0)(1,1)(2,1)(3,1)(2,0)(1,1)(2,1)(3,1)",
  "(0,0)(1,1)(2,2)",
  "(0,0)(1,1)(2,2)(1,0)(2,1)(3,2)",
  "(0,0)(1,1)(2,2)(1,1)",
  "(0,0)(1,1)(2,2)(1,1)(2,0)(3,1)(4,2)",
  "(0,0)(1,1)(2,2)(1,1)(2,2)",
  "(0,0)(1,1)(2,2)(2,0)",
  "(0,0)(1,1)(2,2)(2,0)(3,1)(4,2)",
  "(0,0)(1,1)(2,2)(2,1)",
  "(0,0)(1,1)(2,2)(2,1)(3,2)",
  "(0,0)(1,1)(2,2)(2,2)",
  "(0,0)(1,1)(2,2)(3,0)",
  "(0,0)(1,1)(2,2)(3,1)",
  "(0,0)(1,1)(2,2)(3,1)(4,2)",
  "(0,0)(1,1)(2,2)(3,2)",
  "(0,0)(1,1)(2,2)(3,3)"
];
/** @type {PairSequence[]} */
var testTerms;
function setupTestTerms(){
  // @ts-ignore
  document.getElementById('input').value=initTerms.map(function(e){return "Trans "+e;}).join("\n");
  testTerms=initTerms.map(parsePair);
}
/** @param {boolean} logInfoToConsole */
function testFunction(logInfoToConsole){
  var r={isReduced:[],isStandard:[],Trans:[],TransPreserve:[],TransRev:[],errors:[]};
  /** @type {string?} */
  var lastSuccessPairString=null;
  /** @type {BuchholzTerm?} */
  var lastSuccessBuchholz=null;
  for (var i=0;i<testTerms.length;i++){
    var str=stringifyPair(testTerms[i]);
    var d;
    var caught=false;
    var result;
    if (logInfoToConsole) console.log("%cTesting: isReduced, "+str+".","color:gold");
    d=Date.now();
    try{
      result=isReduced(testTerms[i]);
    }catch(e){
      var diff=Date.now()-d;
      r.isReduced.push({arg0:str,result:e,time:diff});
      r.errors.push({test:"isReduced",arg0:str,name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.isReduced.push({arg0:str,result:stringifyBuchholz(translated),time:diff});
        if (logInfoToConsole) console.log(diff);
        if (!result){
          r.errors.push({test:"isReduced",arg0:str,name:"fail"});
          console.error("Failed test: isReduced, "+str+".");
        }
      }
    }
    if (logInfoToConsole) console.log("%cTesting: isStandard, "+str+".","color:gold");
    d=Date.now();
    try{
      result=isStandardPair(testTerms[i]);
    }catch(e){
      var diff=Date.now()-d;
      r.isStandard.push({arg0:str,result:e,time:diff});
      r.errors.push({test:"isStandard",arg0:str,name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.isStandard.push({arg0:str,result:stringifyBuchholz(translated),time:diff});
        if (logInfoToConsole) console.log(diff);
        if (!result){
          r.errors.push({test:"isStandard",arg0:str,name:"fail"});
          console.error("Failed test: isStandard, "+str+".");
        }
      }
    }
    if (logInfoToConsole) console.log("%cTesting: Trans, "+str+".","color:gold");
    d=Date.now();
    var translated;
    try{
      translated=Trans(testTerms[i]);
      result=isStandardBuchholz(translated);
    }catch(e){
      var diff=Date.now()-d;
      r.Trans.push({arg0:str,result:e,time:diff});
      r.errors.push({test:"Trans",arg0:str,name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.Trans.push({arg0:str,result:stringifyBuchholz(translated),time:diff});
        if (logInfoToConsole) console.log(diff);
        if (!result){
          r.errors.push({test:"Trans",arg0:str,name:"fail"});
          console.error("Failed test: Trans, "+str+".");
        }
      }
    }
    if (caught) continue;
    if (logInfoToConsole) console.log("%cTesting: TransPreserve, "+lastSuccessPairString+", "+str+".","color:gold");
    d=Date.now();
    try{
      result=lessThanBuchholz(lastSuccessBuchholz,translated);
    }catch(e){
      var diff=Date.now()-d;
      r.TransPreserve.push({arg0:lastSuccessPairString,arg1:str,result:e,time:diff});
      r.errors.push({test:"TransPreserve",arg0:lastSuccessPairString,arg1:str,name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.TransPreserve.push({arg0:lastSuccessPairString,arg1:str,result:result,time:diff});
        if (logInfoToConsole) console.log(diff);
        if (!result){
          r.errors.push({test:"TransPreserve",arg0:lastSuccessPairString,arg1:str,name:"fail"});
          console.error("Failed test: TransPreserve, "+lastSuccessPairString+", "+str+".");
        }
      }
    }
    lastSuccessPairString=str;
    lastSuccessBuchholz=translated;
    if (logInfoToConsole) console.log("%cTesting: TransRev, "+str+".","color:gold");
    d=Date.now();
    var revtranslated;
    try{
      revtranslated=TransRev(translated);
      result=equalPair(testTerms[i],revtranslated);
    }catch(e){
      var diff=Date.now()-d;
      r.TransRev.push({arg0:str,result:e,time:diff});
      r.errors.push({test:"TransRev",arg0:str,name:"error",content:e});
      console.error(e);
      caught=true;
    }finally{
      var diff=Date.now()-d;
      if (!caught){
        r.TransRev.push({arg0:str,result:stringifyBuchholz(translated),time:diff});
        if (logInfoToConsole) console.log(diff);
        if (!result){
          r.errors.push({test:"TransRev",arg0:str,name:"fail"});
          console.error("Failed test: TransRev, "+str+".");
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

/** @type {[string,string,string,Function][]} */
var operations=[
  ["Parent","PNN","N",findParent],
  ["Parent","PNNN","Z",isParent],
  ["Ancestor","PNN","[N",findAncestors],
  ["Ancestor","PNNN","Z",isAncestor],
  ["Pred","P","P",Pred],
  ["Derp","P","P",Derp],
  ["[]","P[N","P",function(M){return Array.from(arguments).slice(1).reduce(fundPair,M);}],
  ["IncrFirst","P","P",IncrFirst],
  ["Classify","P","S",function(M){return isZeroPair(M)?"ZT":isPrincipalPair(M)?"PT":"MT";}],
  ["P","P","[P",PPair],
  ["Unadmit","PN","Z",isUnadmitted],
  ["Admit","PN","Z",isAdmitted],
  ["Admitted","P","[N",findAdmitted],
  ["Adm","PN","N",Adm],
  ["Marked","PN","Z",isMarkedPair],
  ["MarkedReduced","PN","Z",isMarkedReduced],
  ["IdxSum","[P","[N",function(){return IdxSum(Array.from(arguments));}],
  ["TrMax","P","N",TrMax],
  ["Br","P","[P",Br],
  ["FirstNodes","P","[N",FirstNodes],
  ["Joints","P","[N",Joints],
  ["Red","P","P",Red],
  ["Reduced","P","Z",isReduced],
  ["Standard","P","Z",isStandardPair],
  ["Standard","PN","Z",isStandardPair],
  ["Descending","[P","Z",function(){return isDescending(Array.from(arguments));}],
  ["Classify","B","S",function(t){return isZeroBuchholz(t)?"0":isPrincipalBuchholz(t)?"PT":"MT";}],
  ["Standard","B","Z",isStandardBuchholz],
  ["[]","B[B","B",function(t){return Array.from(arguments).slice(1).reduce(fundBuchholz,t);}],
  ["P","B","[B",PBuchholz],
  ["RightNodes","B","[N",RightNodes],
  ["scb","BS","SSS",function(t,c){var r=SCBDecomposition(t,c);return r?[r[0],r[1],["Neither","Type 0","Type 1"][isTypeNSCBDecompositionMark(c)+1]]:["-","-","N/A"];}],
  ["scb","BSSS","ZS",function(t,s,c,b){return isSCBDecomposition(t,s,c,b)?[true,["Neither","Type 0","Type 1"][isTypeNSCBDecompositionMark(c)+1]]:[false,"N/A"];}],
  ["scb?","B","S",function(t){return ["Neither","Type 0","Type 1"][isTypeNSCBDecomposable(t)];}],
  ["scb!","B","SSS",function(t){var r=typeNSCBDecomposition(t);return r?[r[1],r[2],r[3],"Type "+r[0]]:["-","-","-","N/A"];}],
  ["Marked","BB","Z",isMarkedBuchholz],
  ["Trans","P","B",Trans],
  ["Mark","PN","B",Mark],
  ["TransType","P","S",function(M){return ["Not reduced","Not principal","j_1=0","Trans(Pred(M))=0","(I)","(II)","(III)","(IV)","(V)","(VI)"][TransType(M)+3];}],
  ["NextAdm","PNN","N",findNextAdm],
  ["NextAdm","PNNN","Z",isNextAdm],
  ["RightAnces","P","[N",RightAnces],
  ["StronglyPrincipal","P","Z",isStronglyPrincipal],
  ["LastStep","P","N",LastStep],
  ["Trans-1","B","P",TransRev],
  ["?","P","P",function(M){return M;}],
  ["?","B","B",function(t){return t;}],
  ["!","P","B",Trans],
  ["!","B","P",TransRev]
];
var input="";
var writeCommonPair=true;
var writeCommonBuchholz=true;
/** @type {([number,*]|Error)[]} */
var last=null;
function compute(recalculate){
  var oldinput=input;
  var inputChanged=false;
  // @ts-ignore
  inputChanged||=input!=document.getElementById("input").value;
  // @ts-ignore
  input=document.getElementById("input").value;
  // @ts-ignore
  inputChanged||=writeCommonPair!=document.getElementById("writeCommonPair").checked;
  // @ts-ignore
  writeCommonPair=document.getElementById("writeCommonPair").checked;
  // @ts-ignore
  inputChanged||=writeCommonBuchholz!=document.getElementById("writeCommonBuchholz").checked;
  // @ts-ignore
  writeCommonBuchholz=document.getElementById("writeCommonBuchholz").checked;
  if (!recalculate&&!inputChanged) return;
  /** @type {Map<string,[number,*]|Error>} */
  var resultMap=new Map();
  if (last){
    var oldlines=oldinput.split(lineBreakRegex);
    for (var l=0;l<oldlines.length;l++){
      resultMap.set(oldlines[l],last[l]);
    }
  }
  last=[];
  var output="";
  var lines=input.split(lineBreakRegex);
  for (var l=0;l<lines.length;l++){
    /** @type {[number,*]|Error} */
    var result;
    if (!resultMap.has(lines[l])){
      var cmd=lines[l].substring(0,lines[l].indexOf(" "));
      var args=lines[l].substring(lines[l].indexOf(" ")+1).split(";");
      try{
        console.time(lines[l]);
        /** @type {string[]} */
        var argtypes=[];
        for (var i=0;i<args.length;i++){
          argtypes.push("S");
          if (integerRegex.test(args[i])) argtypes[i]+="N";
          if (pairSequenceRegex.test(args[i])) argtypes[i]+="P";
          if (buchholzRegex.test(args[i])) argtypes[i]+="B";
        }
        var valid=false;
        for (var i=0;i<operations.length;i++){
          if (operations[i][0].toLowerCase()!=cmd.toLowerCase()) continue;
          var restPos=operations[i][1].indexOf("[");
          if (restPos==-1?operations[i][1].length!=args.length:restPos>args.length) continue;
          var match=true;
          for (var j=0;j<args.length;j++){
            var argumentType=restPos!=-1&&j>=restPos?operations[i][1][restPos+1]:operations[i][1][j];
            if (argtypes[j].indexOf(argumentType)==-1){
              match=false;
              break;
            }
          }
          if (!match) continue;
          var convertedArgs=[];
          for (var j=0;j<args.length;j++){
            var argumentType=restPos!=-1&&j>=restPos?operations[i][1][restPos+1]:operations[i][1][j];
            if (argumentType=="N") convertedArgs.push(+args[j]);
            else if (argumentType=="P") convertedArgs.push(parsePair(args[j]));
            else if (argumentType=="B") convertedArgs.push(parseBuchholz(args[j]));
            else if (argumentType=="S") convertedArgs.push(args[j]);
          }
          result=[i,operations[i][3].apply(null,convertedArgs)];
          valid=true;
          break;
        }
        if (!valid) throw Error("No matching operation found: "+cmd+" "+argtypes.join(";"));
        console.timeEnd(lines[l]);
      }catch(e){
        result=e;
        console.error(e);
      }
      resultMap.set(lines[l],result);
    }else result=resultMap.get(lines[l]);
    last[l]=result;
    output+=lines[l]+"\n";
    if (result instanceof Error){
      output+=result.stack?result.stack:result;
    }else{
      var i=result[0];
      /** @type {Array} */
      var resultArray;
      if (operations[result[0]][2].length==1) resultArray=[result[1]];
      else resultArray=result[1];
      var restPos=operations[i][2].indexOf("[");
      for (var j=0;j<resultArray.length;j++){
        if (j>0) output+=";";
        var resultType=restPos!=-1&&j>=restPos?operations[i][2][restPos+1]:operations[i][2][j];
        if (resultType=="N") output+=resultArray[j];
        else if (resultType=="Z") output+=resultArray[j];
        else if (resultType=="P") output+=stringifyPair(resultArray[j],writeCommonPair);
        else if (resultType=="B") output+=stringifyBuchholz(resultArray[j],writeCommonBuchholz);
        else if (resultType=="S") output+=resultArray[j];
      }
    }
    output+="\n\n";
  }
  // @ts-ignore
  document.getElementById("output").value=output;
}
var hasRequestedCompute=false;
function requestCompute(){
  if (!hasRequestedCompute){
    requestAnimationFrame(function(){hasRequestedCompute=false;compute();});
    hasRequestedCompute=true;
  }
}
var handlekey=function(e){requestCompute();};
