var lineBreakRegex=/\r?\n/g;
var itemSeparatorRegex=/[\t ,]/g;
window.onload=function (){
  console.clear();
  dg('input').onkeydown=handlekey;
  dg('input').onfocus=handlekey;
  dg('input').onmousedown=handlekey;
  load();
  convertall();
}
function dg(s){
  return document.getElementById(s);
}
function parseMatrix(s){
  if (!/^(\(\d*(,\d*)*\))*$/.test(s)) return [];
  var matrix=JSON.parse(
    "["+s
      .replace(itemSeparatorRegex,",")
      .replace(/\(/g,"[")
      .replace(/\)/g,"]")
      .replace(/\]\[/g,"],[")+"]");
  var columns=matrix.length;
  var rows=0;
  for (var i=0;i<columns;i++){
    if (matrix[i].length>rows){
      rows=matrix[i].length;
    }
  }
  for (var i=0;i<columns;i++){
    while (matrix[i].length<rows){
      matrix[i].push(0);
    }
  }
  return matrix;
}
function cloneMatrix(matrix){
  var newMountain=[];
  for (var i=0;i<matrix.length;i++) newMountain.push(mountain[i].slice(0));
  return newMountain;
}
var DIRECTION="Y";
//function Y_to_B(s){}
function B_to_Y(s){
  var matrix;
  if (typeof s=="string") matrix=parseMatrix(s);
  else matrix=cloneMatrix(s);
  var X=matrix.length;
  var Y=matrix[0].length;
  var parentMatrix=[];
  for (var y=0;y<Y;y++){
    for (var x=0;x<X;x++){
      var p;
      if (y===0){
        parentMatrix.push([]);
        for (p=x;p>=0;p--)
          if (matrix[p][y]<matrix[x][y]) break;
      }else{
        for (p=x;p>=0;p=parentMatrix[p][y-1])
          if (matrix[p][y]<matrix[x][y]) break;
      }
      parentMatrix[x][y]=p;
    }
  }
  var a=[];
  for (var x=0;x<X;x++) a.push(1);
  for (var y=Y-1;y>=0;y--){
    for (var x=0;x<X;x++){
      a[x]=matrix[x][y]===0?1:a[x]+a[parentMatrix[x][y]];
    }
  }
  return a.join(",");
}
var input="";
function convertall(recalculate){
  if (!recalculate&&input==dg("input").value) return;
  input=dg("input").value;
  dg("output").value=input.split(lineBreakRegex).map(DIRECTION=="B"?Y_to_B:B_to_Y).join("\r\n");
}
function toggledirection(){
  if (DIRECTION=="B"){
    DIRECTION="Y";
    dg("toggledirectionbutton").value="BMS->0-Y";
  }else{
    DIRECTION="B";
    dg("toggledirectionbutton").value="0-Y->BMS";
  }
  convertall(true);
}
function swap(){
  dg("input").value=dg("output").value;
  toggledirection();
}
window.onpopstate=function (e){
  load();
  convertall(true);
}
function save(clipboard){
  var encodedInput;
  if (DIRECTION=="B"){
    var encodedInput=input.split(lineBreakRegex).map(e=>e.split(itemSeparatorRegex).map(parseSequenceElement).map(e=>e.value)).join(";")+";"+DIRECTION;
  }else if (DIRECTION=="Y"){
    var encodedInput=input.split(lineBreakRegex).map(e=>parseMatrix(e).map(e=>e.join(",").replace(/(,0)+$/,"")).join("_")).join(";")+";"+DIRECTION;
  }
  history.pushState(encodedInput,"","?"+encodedInput);
  if (clipboard){
    var copyarea=dg("copyarea");
    copyarea.value=location.href;
    copyarea.style.display="";
    copyarea.select();
    copyarea.setSelectionRange(0,99999);
    document.execCommand("copy");
    copyarea.style.display="none";
  }
}
function load(){
  var state=location.search.substring(1);
  if (!state) return;
  var input=state.split(";");
  if (["B","Y"].includes(input[input.length-1])) DIRECTION=input.pop();
  if (DIRECTION=="B"){
    input=input.join("\r\n");
    dg("toggledirectionbutton").value="0-Y->BMS";
  }else{
    input=input.map(e=>"("+e.replace(/_/g,")(")+")").join("\r\n");
    dg("toggledirectionbutton").value="BMS->0-Y";
  }
  dg("input").value=input;
}
var handlekey=function(e){
  setTimeout(convertall,0);
}