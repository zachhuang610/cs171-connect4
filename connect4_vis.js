const d3 = require('d3')
d3.selectAll("svg > *").remove();

function printValue(row, col, xoffset, yoffset, value) {
    if (String(value) === 'X') {
        d3.select(svg)
        .append("text")
        .style("fill", "black")
        .attr("x", (col)*10 + xoffset)
        .attr("y", (row)*14 + yoffset)
        .text('O');
    }
    else if (String(value) === 'O') {
        d3.select(svg)
        .append("text")
        .style("fill", "red")
        .attr("x", (col)*10 + xoffset)
        .attr("y", (row)*14 + yoffset)
        .text('O');
    }
  
}

function printState(stateAtom, xoffset, yoffset) {
  for (r = 0; r <= 6; r++) {
    for (c = 0; c <= 6; c++) {
      printValue(r, c, xoffset, yoffset,
                 stateAtom.board[6-r][6-c]
                 .toString().substring(0,1))  
    }
  }
  
  d3.select(svg)
    .append('rect')
    .attr('x', xoffset)
    .attr('y', yoffset+1)
    .attr('width', 77)
    .attr('height', 85)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
}


var xoffset = 0
var yoffset = 0
for(b = 0; b <= 20; b++) {  
  if(Board.atom("Board"+b) != null)
    printState(Board.atom("Board"+b), xoffset, yoffset)
  xoffset = xoffset + 90 
  if (xoffset > 500) {
	xoffset = 0
	yoffset = yoffset + 110
  }
}
