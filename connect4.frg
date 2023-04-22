#lang forge/bsl

abstract sig Player{}
one sig X, O extends Player{}

abstract sig Index {}
one sig A extends Index {}
one sig B extends Index {}
one sig C extends Index {}
one sig D extends Index {}
one sig E extends Index {}
one sig F extends Index {}
one sig G extends Index {}

sig Board {
    places: pfunc Index -> Index -> Player
}

one sig Game {
    initialState: one Board,
    next: pfunc Board -> Board
}

// Basic wellformedness check
pred wellformed[b: Board] {
    all row, col: Int | {
        (row < 0 or row > 7 or col < 0 or col > 7) implies
        no b.board[row][col]
    }
}

// Packages wellformed into a pred applying to all Boards, for ease of reference
pred allWellformed {
    all b: Board{
        wellformed[b]
    }
}

fun countPiece[brd: Board, p: Player]: one Int {
  #{r,c: Index | brd.places[r][c] = p}
}

// Checks if it is X's turn (X starts)
pred Xturn[b: Board] {
    // Same number of X and O on board
    countPiece[b, X] = countPiece[b, O]
}

// Checks if it is O's turn
pred Oturn[b: Board] {
    subtract[countPiece[b, X],1] = countPiece[b, O]
}

// defines starting state
pred starting[b: Board] {
    all r, c: Index | no b.places[r][c]
}

pred winH[b: Board, p: Player] {
    some r: Index | all c: Index |
        b.places[r][c] = p
}

pred winV[b: Board, p: Player] {
    some c: Index | all r: Index |
        b.places[r][c] = p
}

pred winD[b: Board, p: Player] {
    (b.places[A][A] = p and 
     b.places[B][B] = p and
     b.places[C][C] = p)
    or
    (b.places[A][C] = p and 
     b.places[B][B] = p and
     b.places[C][A] = p)
}

// Defines the win condition (player eats poisoned (0,0) square)
pred winning[b: Board, p: Player] {
  winH[b, p] or winV[b, p] or winD[b, p]
}

// Defines a valid move
pred move[pre: Board, post: Board, p: Player, r: Index, c: Index] {
    -- GUARD (required to be able to make the move): 
    no pre.places[r][c]         -- no move there yet
    p = X implies xturn[pre]    -- correct turn
    p = O implies oturn[pre]    -- correct turn
	-- TRANSITION (what does the post-move board look like?)
    --     Add the mark:
	post.places[r][c] = p    
    --     Assert that no other squares change (this is called a "frame condition"):
    all r2, c2: Index | (r2!=r or c2!=c) implies {
        post.places[r2][c2] = pre.places[r2][c2]
    }
}

// pred doNothing[pre: Board, post: Board] {
//     // If some player has lost
//     some p: Player | lost[pre, p]

//     // Change nothing
//     all row2: Int, col2: Int | 
//         post.board[row2][col2] = pre.board[row2][col2]
// }

pred traces {
    // Start at initial state
    starting[Game.initialState]

    // All other states are reached by move or doNothing
    all b: Board | some Game.next[b] implies {
        some row, col: Index, p: Player | {
            move[b, Game.next[b], p, row, col]            
        }
        // or
        //     doNothing[b, Game.next[b]]
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
