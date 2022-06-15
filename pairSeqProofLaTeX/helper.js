var lineBreakRegex=/\r?\n/gu;
var whitespaceRegex=/[ \t\n\r]/gu;
var leadingWhitespaceRegex=/^[ \t\n\r]+/u;
var trailingWhitespaceRegex=/[ \t\n\r]+$/u;
/**
 * @param {string} input 
 * @returns {string}
 */
function removeLeadingAndTrailingWhitespace(input){
  return input
    .replace(leadingWhitespaceRegex,"")
    .replace(trailingWhitespaceRegex,"");
}
/**
 * @param {string} input
 * @param {boolean=} nocleanlines 
 * @returns {string[]}
 */
function splitLines(input,nocleanlines){
  return removeLeadingAndTrailingWhitespace(input).split(lineBreakRegex).map(s=>nocleanlines?s:removeLeadingAndTrailingWhitespace(s));
}
/**
 * @param {string} input 
 * @param {number} level
 * @returns {string}
 */
function indent(input,level){
  return splitLines(input,true).map(s=>(s&&level?"\t".repeat(level):"")+s).join("\n");
}
function escapeBrackets(input){
  return input
    .replace(/\[(?=[^ 0-9\\%$_#&()[\]{}])/gu,"\\lbrack ")
    .replace(/\[/gu,"\\lbrack")
    .replace(/\](?=[^ 0-9\\%$_#&()[\]{}])/gu,"\\rbrack ")
    .replace(/\]/gu,"\\rbrack");
}
/**
 * @param {string[]} lines 
 * @param {string} indentSymbol 
 * @returns {number}
 */
function findIndentedEndLine(lines,indentSymbol){
  var inenvironments=0;
  return lines.findIndex(s=>{
    if (s.startsWith("\\begin")||inenvironments>0) inenvironments+=s.match(/\\begin/gu)?.length||0;
    var inenvironment=inenvironments>0;
    if (s.startsWith("\\end")||inenvironments>0) inenvironments-=s.match(/\\end/gu)?.length||0;
    return !inenvironment&&!s.startsWith(indentSymbol);
  });
}
/**
 * @param {string} input 
 * @param {number} startIndex 
 * @param {string} indentSymbol 
 * @returns {number}
 */
function findIndentedEnd(input,startIndex,indentSymbol){
  var endLine=findIndentedEndLine(splitLines(input.substring(startIndex),true),indentSymbol);
  if (endLine==-1) return input.length;
  var r=startIndex;
  for (var i=0;i<endLine;i++) r+=input.substring(r).search(lineBreakRegex)+(i<endLine-1?1:0);
  return r;
}
/**
 * @param {string} input 
 * @returns {string}
 */
function convert(input){
  var r="";
  for (var i=0;i<input.length;){
    var rest=input.substring(i);
    var lineStart=i==0||input[i-1].search(lineBreakRegex)!=-1;
    if (rest.startsWith("{|")) r+=converttheorem(input.substring(i,i=input.indexOf("|}",i)+2));
    else if (lineStart&&rest.startsWith("; ")&&/^; (?:.+の)?証明[:：]$/u.test(rest.substring(0,rest.search(lineBreakRegex)))) r+=convertproof(input.substring(i,i+=findIndentedEnd(rest,rest.search(lineBreakRegex)+1,":")));
    else if (lineStart&&rest.startsWith("#")) r+=convertnenumerate(input.substring(i,i+=findIndentedEnd(rest,0,"#")));
    else if (lineStart&&rest.startsWith(":")) r+=convertindented(input.substring(i,i+=findIndentedEnd(rest,0,":")));
    else if (lineStart&&rest.startsWith("=")) r+=convertsection(input.substring(i,i+=rest.search(lineBreakRegex)));
    else if (rest.startsWith("<ref>")) r+=convertfootnote(input.substring(i,i+=rest.search("</ref>")+6));
    else if (rest.startsWith("[[#")) r+=convertnameref(input.substring(i,i=input.indexOf("]]",i)+2));
    else r+=rest[0],i++;
  }
  return r;
}
/**
 * @param {string} input 
 * @returns {[string,string[]]}
 */
function extractFootnotes(input){
  var r="";
  /** @type {string[]} */
  var footnotes=[];
  for (var i=0;i<input.length;){
    var rest=input.substring(i);
    if (rest.startsWith("\\footnote{")){
      for (var j=i+10,braces=1;j<input.length&&braces>0;j++){
        if ((input[j]=="{"||input[j]=="}")&&(j-input.substring(0,j).search(/\\*$/u))%2==0) braces+=input[j]=="{"?1:-1;
      }
      r+="\\footnotemark{}";
      footnotes.push(input.substring(i+10,j-1));
      i=j;
    }else r+=rest[0],i++;
  }
  return [r,footnotes];
}
/**
 * @param {string} input 
 * @returns {string}
 */
function converttheorem(input){
  var header=removeLeadingAndTrailingWhitespace(input.substring(input.indexOf("!")+1,input.indexOf("|-")));
  var body=input.substring(input.indexOf("|",input.indexOf("|-")+1)+1,input.indexOf("|}"));
  var [_,type,label,name]=/(.+?)[\(（]?<span id=['"](.+)['"]>(.+)<\/span>[\)）]?/u.exec(header).map(removeLeadingAndTrailingWhitespace);
  var types={
    "定理":"theorem",
    "命題":"proposition",
    "補題":"lemma",
    "系":"corollary"
  };
  var [convertedbody,footnotes]=extractFootnotes(convert(body));
  return `\\begin{${types[type]}}[${escapeBrackets(name)}]\\label{${label}}\n${indent(convertedbody,1)}\n\\end{${types[type]}}${footnotes.length==0?"":(footnotes.length==1?"":`\n\\addtocounter{footnote}{${1-footnotes.length}}`)+footnotes.map(s=>`\n\\footnotetext{${s}}`).join("\n\\addtocounter{footnote}{1}")}`;
}
/**
 * @param {string} input 
 * @returns {string}
 */
function convertnenumerate(input){
  var lastLevel=0;
  var inenvironments=0;
  return splitLines(input).map((s,i,a)=>{
      if (s.startsWith("\\begin")||inenvironments>0) inenvironments+=s.match(/\\begin/gu)?.length||0;
      var inenvironment=inenvironments>0;
      if (s.startsWith("\\end")||inenvironments>0) inenvironments-=s.match(/\\end/gu)?.length||0;
    if (inenvironment) return indent(s,lastLevel);
    var [_,head,rest]=/^(#*)(.+)$/u.exec(removeLeadingAndTrailingWhitespace(s)).map(removeLeadingAndTrailingWhitespace);
    var r="";
    var level=head.length;
    while (lastLevel<level) r+=indent("\\begin{nenumerate}",lastLevel++)+"\n";
    while (lastLevel>level) r+=indent("\\end{nenumerate}",--lastLevel)+"\n";
    r+=indent("\\item "+convert(rest),level);
    if (i==a.length-1) while (lastLevel) r+="\n"+indent("\\end{nenumerate}",--lastLevel);
    return r;
  }).join("\n");
}
/**
 * @param {string} input 
 * @returns {string}
 */
function convertindented(input){
  var lines=splitLines(input);
  if (lines.some(s=>/^: *\(\d+\) /.test(s))) return convertpenumerate(input);
  var r="\\begin{indented}";
  var inenvironments=0;
  for (var i=0;i<lines.length;){
    var s=lines[i];
    if (s.startsWith("\\begin")||inenvironments>0) inenvironments+=s.match(/\\begin/gu)?.length||0;
    var inenvironment=inenvironments>0;
    if (s.startsWith("\\end")||inenvironments>0) inenvironments-=s.match(/\\end/gu)?.length||0;
    if (inenvironment) r+="\n"+indent(s,1),i++;
    else{
      var rest=removeLeadingAndTrailingWhitespace(s.substring(1));
      if (rest.startsWith(":")){
        if (i==0) r+="\n"+indent("\\item",1);
        var j=findIndentedEndLine(lines.slice(i),"::");
        r+="\n"+indent(convertindented(lines.slice(i,i=j==-1?lines.length:i+j).map(s=>s[0]==":"?s.substring(1):s).join("\n")),1);
      }else if (/^\([0-9-a-zA-Z]+\) /u.test(rest)){
        var [_,num,body]=/^\(([0-9-a-zA-Z]+)\) (.+)$/u.exec(removeLeadingAndTrailingWhitespace(rest)).map(removeLeadingAndTrailingWhitespace);
        r+="\n"+indent(`\\item[(${num})] ${convert(body)}`,1),i++;
      }else r+="\n"+indent("\\item "+convert(rest),1),i++;
    }
  }
  r+="\n\\end{indented}";
  return r;
}
/**
 * @param {string} input 
 * @returns {string}
 */
function convertpenumerate(input){
  var lines=splitLines(input);
  var r="\\begin{penumerate}";
  var lastNum=0;
  var inenvironments=0;
  for (var i=0;i<lines.length;){
    var s=lines[i];
    if (s.startsWith("\\begin")||inenvironments>0) inenvironments+=s.match(/\\begin/gu)?.length||0;
    var inenvironment=inenvironments>0;
    if (s.startsWith("\\end")||inenvironments>0) inenvironments-=s.match(/\\end/gu)?.length||0;
    if (inenvironment) r+="\n"+indent(s,1),i++;
    else{
      var rest=removeLeadingAndTrailingWhitespace(s.substring(1));
      if (rest.startsWith(":")){
        if (i==0) r+="\n"+indent("\\item",1);
        var roman=["i","ii","iii","iv","v","vi","vii","viii"];
        var j=findIndentedEndLine(lines.slice(i),"::");
        r+="\n"+indent(convertindented(lines.slice(i,i=j==-1?lines.length:i+j).map(s=>s[0]==":"?s.substring(1):s).join("\n")).replace(/\\setcounter{penumerate([iv]+)}/g,(_,s)=>`\\setcounter{penumerate${roman[roman.indexOf(s)+1]}}`),1);
      }else if (/^\([0-9-a-zA-Z]+\) /u.test(rest)){
        var [_,num,body]=/^\(([0-9-a-zA-Z]+)\) (.+)$/u.exec(removeLeadingAndTrailingWhitespace(rest)).map(removeLeadingAndTrailingWhitespace);
        if (/^\d+$/u.test(num)){
          if (+num!=lastNum+1) r+="\n"+indent(`\\setcounter{penumeratei}{${+num-1}}`,1);
          lastNum=+num;
          r+="\n"+indent("\\item "+convert(body),1),i++;
        }else r+="\n"+indent(`\\item[(${num})] ${convert(body)}`,1),i++;
      }else r+="\n"+indent("\\item[] "+convert(rest.replace(/^: */u,"")),1),i++;
    }
  }
  r+="\n\\end{penumerate}";
  return r;
}
/**
 * @param {string} input 
 * @returns {string}
 */
function convertproof(input){
  var lines=splitLines(input);
  var [_,title]=/^; ((?:.+の)?証明)[:：]$/u.exec(lines[0]);
  lines[lines.length-1]=lines[lines.length-1].replace(/□$/u,"");
  return `\\begin{hideableproof}${title=="証明"?"":`[${escapeBrackets(convert(title))}]`}\n${indent(convertindented(lines.slice(1).join("\n")),1)}\n\\end{hideableproof}`;
}
/**
 * @param {string} input 
 * @returns {string}
 */
function convertsection(input){
  var [_,symbol,title]=/^(=+)(.+?)=+$/u.exec(input).map(removeLeadingAndTrailingWhitespace);
  var commands=["section","subsection","subsubsection"];
  return `\\${commands[symbol.length-1]}{${title}}`;
}
/**
 * @param {string} input 
 * @returns {string}
 */
function convertfootnote(input){
  var [_,body]=/<ref>(.+?)<\/ref>/u.exec(input).map(removeLeadingAndTrailingWhitespace);
  return `\\footnote{${convert(body)}}`;
}
/**
 * @param {string} input 
 * @returns {string}
 */
function convertnameref(input){
  var [_,label]=/\[\[#([^|]+).+?\]\]/u.exec(input).map(removeLeadingAndTrailingWhitespace);
  return `\\nameref{${label}}`;
}