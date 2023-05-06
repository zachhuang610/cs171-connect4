#lang forge

option problem_type temporal
option max_tracelength 7

abstract sig Player{}
one sig X, O extends Player{}

one sig Board {
    var board: pfunc Int -> Int -> Player 
}

// Basic wellformedness check
pred wellformed {
    all row, col: Int | {
        (row < 0 or row > 6 or col < 0 or col > 6) implies
        no Board.board[row][col]
    }
}

// Packages wellformed into a pred applying to all Boards, for ease of reference

// Checks if it is X's turn (X starts)
pred Xturn {
    // Same number of X and O on board
    #{row, col: Int | Board.board[row][col] = X} = 
    #{row, col: Int | Board.board[row][col] = O}
}

// Checks if it is O's turn
pred Oturn {
    #{row, col: Int | Board.board[row][col] = X} = 
    add[#{row, col: Int | Board.board[row][col] = O}, 1]
}

// Defines the initial board (no marks made)
pred init {
    all row, col: Int | 
        no Board.board[row][col]
}

pred wonH[p: Player] {
    some row, col: Int | col < 4 and col >= 0 => {
        Board.board[row, col] = p
        Board.board[row, add[col, 1]] = p
        Board.board[row, add[col, 2]] = p
        Board.board[row, add[col, 3]] = p
    }
}

pred wonV[p: Player] {
    some row, col: Int | row < 4 and row >= 0 => {
        Board.board[row, col] = p
        Board.board[add[row, 1], col] = p
        Board.board[add[row, 2], col] = p
        Board.board[add[row, 3], col] = p
    }
}

pred wonDUpwards[p: Player] {
    some row, col: Int | row < 4 and row >= 0 and col < 4 and col >= 0 => {
        Board.board[row, col] = p
        Board.board[add[row, 1], add[col, 1]] = p
        Board.board[add[row, 2], add[col, 2]] = p
        Board.board[add[row, 3], add[col, 3]] = p
    }
}

pred wonDDownwards[p: Player] {
    some row, col: Int | row <=6 and row > 2 and col < 4 and col >= 0 => {
        Board.board[row, col] = p
        Board.board[subtract[row, 1], add[col, 1]] = p
        Board.board[subtract[row, 2], add[col, 2]] = p
        Board.board[subtract[row, 3], add[col, 3]] = p
    }
}

// Defines the win condition (player wins horizontally, vertically, or diagonally)
pred won[p: Player] {
    wonH[p] or wonV[p] or wonDUpwards[p] or wonDDownwards[p]
}

// Defines a valid move
pred move[row: Int, col: Int, p: Player] { 
    // no move already there
    no Board.board[row][col] 
    // appropriate turn
    p = X implies Xturn
    p = O implies Oturn  

    // There is either a piece below it or it is at row = 0;
	row = 0 or one Board.board[subtract[row, 1]][col]

    // Take the move
    next_state Board.board[row][col] = p

    // Nothing else changes
    all row2: Int, col2: Int | (row!=row2 or col!=col2) implies {                
        next_state Board.board[row2][col2] = Board.board[row2][col2]     
    } 
}

pred doNothing {
    // If some player has won
    some p: Player | won[p]

    // Change nothing
    all row2: Int, col2: Int | 
        next_state Board.board[row2][col2] = Board.board[row2][col2]
}

pred traces {
    // Start at initial state
	always wellformed
	some row, col: Int | {
		{move[row,col,X] or move[row,col,O]} until {won[X] or won[O]}}
}


test expect {traces is unsat}

