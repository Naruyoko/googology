/// <reference path="./common.js" />

var lineBreakRegex=/\r?\n/g;

window.onload=function (){
  var initTerms=[
    "(0,0)(1,1)(2,2)(3,0)(4,1)",
    "(1,1)(2,1)(1,0)(2,2)(3,3)"
  ];
  // @ts-ignore
  document.getElementById('input').value=initTerms.join("\n");
}

function compute(){
  // @ts-ignore
  var input=document.getElementById("input").value;
  // @ts-ignore
  var writeCommonPair=document.getElementById("writeCommonPair").checked;
  // @ts-ignore
  var writeCommonBuchholz=document.getElementById("writeCommonBuchholz").checked;
  /** @type {HTMLDivElement} */
  // @ts-ignore
  var output=document.getElementById("output");
  output.innerHTML="";
  var lines=input.split(lineBreakRegex);
  for (var l=0;l<lines.length;l++){
    var M=parsePair(lines[l]);
    if (M.length==0) break;
    var mel=document.createElement("div");
    output.appendChild(mel);
    mel.innerHTML+="<p>"+stringifyPair(M,writeCommonPair)+"</p>";
    if (!isReduced(M)){
      M=Red(M);
      mel.innerHTML+="<p>Reduced to "+stringifyPair(M,writeCommonPair)+"</p>";
    }
    var pTerms=PPair(M);
    for (var i=0;i<pTerms.length;i++){
      var pel=document.createElement("div");
      mel.appendChild(pel);
      if (pTerms.length>1) pel.innerHTML+=stringifyPair(pTerms[i],writeCommonPair);
      var tcel=document.createElement("div");
      pel.appendChild(tcel);
      var table=document.createElement("table");
      tcel.appendChild(table);
      table.className="table";
      var row=document.createElement("tr");
      table.appendChild(row);
      row.innerHTML+="<th>m</th>";
      for (var j=0;j<pTerms[i].length;j++)
        row.innerHTML+="<th>"+j+"<br>("+pTerms[i][j][0]+","+pTerms[i][j][1]+")</th>";
      /** @type {[number,number][]} */
      var jMemo=[];
      var row=document.createElement("tr");
      table.appendChild(row);
      row.innerHTML+="<td></td>";
      for (var j=0;j<pTerms[i].length;j++){
        var N=pTerms[i].slice(0,j+1);
        if (j==0) row.innerHTML+="<td></td>";
        else{
          var j0=findParent(N,0,j);
          var jn1=Adm(N,j0);
          jMemo[j]=[j0,jn1];
          var type=TransType(N);
          row.innerHTML+="\
            <td>\
              j<sub>0</sub>="+j0+"<br>\
              j<sub>-1</sub>="+jn1+"<br>\
              "+(type==0?"Trans(Pred(M))=0":"Type ("+["I","II","III","IV","V","VI"][type-1]+")")+"\
            </td>";
        }
      }
      for (var m=0;m<pTerms[i].length;m++){
        var row=document.createElement("tr");
        table.appendChild(row);
        row.innerHTML+="<td>"+m+"</td>";
        for (var j=0;j<pTerms[i].length;j++){
          var N=pTerms[i].slice(0,j+1);
          var cell=document.createElement("td");
          row.appendChild(cell);
          if (m<=j&&isMarkedPair(N,m)) cell.textContent=stringifyBuchholz(Mark(N,m),writeCommonBuchholz);
          if (j==0) void 0;
          else if (m==jMemo[j][1]) cell.style.backgroundColor="yellow";
          else if (m==jMemo[j][0]) cell.style.backgroundColor="cyan";
        }
      }
    }
    if (pTerms.length>1){
      var oneReplaceMark="<del>"+stringifyBuchholz(BUCHHOLZ_ZERO,writeCommonBuchholz)+"</del>"+
        "<ins>"+stringifyBuchholz(BUCHHOLZ_ONE,writeCommonBuchholz)+"</ins>";
      mel.innerHTML+="\
        <p>\
          Trans(M)="+pTerms.map(function(e,i){return i>0&&equalPair(e,[[0,0]])?oneReplaceMark:stringifyBuchholz(Trans(e),writeCommonBuchholz);}).join("+")+"<br>\
          ="+stringifyBuchholz(Trans(M),writeCommonBuchholz)+"\
        </p>";
    }else mel.innerHTML+="<p>Trans(M)="+stringifyBuchholz(Trans(M),writeCommonBuchholz)+"</p>";
  }
}