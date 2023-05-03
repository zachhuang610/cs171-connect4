const d3 = require('d3')
d3.selectAll("svg > *").remove();

function printValue(row, col, yoffset, value) {
  d3.select(svg)
    .append("text")
    .style("fill", "black")
    .attr("x", (col)*10)
    .attr("y", (row)*14 + yoffset)
    .text(value);
}

function printState(stateAtom, yoffset) {
  for (r = 0; r <= 7; r++) {
    for (c = 0; c <= 7; c++) {
      printValue(r, c, yoffset,
                 stateAtom.board[7-r][7-c]
                 .toString().substring(0,1))  
    }
  }
  
  d3.select(svg)
    .append('rect')
    .attr('x', 5)
    .attr('y', yoffset+1)
    .attr('width', 77)
    .attr('height', 100)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
}


var offset = 0
for(b = 0; b <= 10; b++) {  
  if(Board.atom("Board"+b) != null)
    printState(Board.atom("Board"+b), offset)  
  offset = offset + 150
}