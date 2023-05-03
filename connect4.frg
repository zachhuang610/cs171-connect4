#lang forge/bsl

abstract sig Player{}
one sig X, O extends Player{}

sig Board {
    board: pfunc Int -> Int -> Player
}

one sig Game {
    initialState: one Board,
    next: pfunc Board -> Board
}

// Basic wellformedness check
pred wellformed[b: Board] {
    all row, col: Int | {
        (row < 0 or row > 6 or col < 0 or col > 6) implies
        no b.board[row][col]
    }
}

// Packages wellformed into a pred applying to all Boards, for ease of reference
pred allWellformed {
    all b: Board{
        wellformed[b]
    }
}

// Checks if it is X's turn (X starts)
pred Xturn[b: Board] {
    // Same number of X and O on board
    #{row, col: Int | b.board[row][col] = X} = 
    #{row, col: Int | b.board[row][col] = O}
}

// Checks if it is O's turn
pred Oturn[b: Board] {
    #{row, col: Int | b.board[row][col] = X} = 
    add[#{row, col: Int | b.board[row][col] = O}, 1]
}

// Defines the initial board (no marks made)
pred starting[b: Board] {
    all row, col: Int | 
        no b.board[row][col]
}

pred wonH[b: Board, p: Player] {
    some row, col: Int | col < 4 and col >= 0 => {
        b.board[row, col] = p
        b.board[row, add[col, 1]] = p
        b.board[row, add[col, 2]] = p
        b.board[row, add[col, 3]] = p
    }
}

pred wonV[b: Board, p: Player] {
    some row, col: Int | row < 4 and row >= 0 => {
        b.board[row, col] = p
        b.board[add[row, 1], col] = p
        b.board[add[row, 2], col] = p
        b.board[add[row, 3], col] = p
    }
}

pred wonDUpwards[b: Board, p: Player] {
    some row, col: Int | row < 4 and row >= 0 and col < 4 and col >= 0 => {
        b.board[row, col] = p
        b.board[add[row, 1], add[col, 1]] = p
        b.board[add[row, 2], add[col, 2]] = p
        b.board[add[row, 3], add[col, 3]] = p
    }
}

pred wonDDownwards[b: Board, p: Player] {
    some row, col: Int | row <=6 and row > 2 and col < 4 and col >= 0 => {
        b.board[row, col] = p
        b.board[subtract[row, 1], add[col, 1]] = p
        b.board[subtract[row, 2], add[col, 2]] = p
        b.board[subtract[row, 3], add[col, 3]] = p
    }
}

// Defines the win condition (player wins horizontally, vertically, or diagonally)
pred won[b: Board, p: Player] {
    wonH[b, p] or wonV[b, p] or wonDUpwards[b, p] or wonDDownwards[b, p]
}

// Defines a valid move
pred move[pre: Board, post: Board, row: Int, col: Int, p: Player] { 
    // no move already there
    no pre.board[row][col] 
    // appropriate turn
    p = X implies Xturn[pre]
    p = O implies Oturn[pre]  

    // There is either a piece below it or it is at row = 0;
	row = 0 or one pre.board[subtract[row, 1]][col]

    // Take the move
    post.board[row][col] = p

    // Nothing else changes
    all row2: Int, col2: Int | (row!=row2 or col!=col2) implies {                
        post.board[row2][col2] = pre.board[row2][col2]     
    } 
}

pred doNothing[pre: Board, post: Board] {
    // If some player has won
    some p: Player | won[pre, p]

    // Change nothing
    all row2: Int, col2: Int | 
        post.board[row2][col2] = pre.board[row2][col2]
}

pred traces {
    // Start at initial state
    starting[Game.initialState]

    // All other states are reached by move or doNothing
    all b: Board | some Game.next[b] implies {
        some row, col: Int, p: Player | {
            move[b, Game.next[b], row, col, p]            
        }
        // or
        // doNothing[b, Game.next[b]]
    }
}

// Example run 
// (see tests for more, particularly test expects that check winning) – this 
// run is really just for demonstration, and it's possible that no one wins yet
// with 10 Board. We show that someone will win eventually in testing.
run {
    allWellformed
    traces
} for 10 Board for {next is linear}
