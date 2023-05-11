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
    some row, col: Int | col < 4 and col >= 0 and row >= 0 and row <= 6 => {
        b.board[row, col] = p
        b.board[row, add[col, 1]] = p
        b.board[row, add[col, 2]] = p
        b.board[row, add[col, 3]] = p
    }
}

pred wonV[b: Board, p: Player] {
    some row, col: Int | row < 4 and row >= 0 and col >= 0 and col <= 6=> {
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
    // wonH[b, p]
    // or
    // wonV[b, p]
    // or
    {
        b.board[0,0] = p
        b.board[1,0] = p
        b.board[2,0] = p
        b.board[3,0] = p
    }
    or
    {
        b.board[1,0] = p
        b.board[2,0] = p
        b.board[3,0] = p
        b.board[4,0] = p
    }
    or
    {
        b.board[2,0] = p
        b.board[3,0] = p
        b.board[4,0] = p
        b.board[5,0] = p
    }
    or
    {
        b.board[3,0] = p
        b.board[4,0] = p
        b.board[5,0] = p
        b.board[6,0] = p
    }
    or
    {
        b.board[0,1] = p
        b.board[1,1] = p
        b.board[2,1] = p
        b.board[3,1] = p
    }
    or
    {
        b.board[1,1] = p
        b.board[2,1] = p
        b.board[3,1] = p
        b.board[4,1] = p
    }
    or
    {
        b.board[2,1] = p
        b.board[3,1] = p
        b.board[4,1] = p
        b.board[5,1] = p
    }
    or
    {
        b.board[3,1] = p
        b.board[4,1] = p
        b.board[5,1] = p
        b.board[6,1] = p
    }
    or
    {
        b.board[0,2] = p
        b.board[1,2] = p
        b.board[2,2] = p
        b.board[3,2] = p
    }
    or
    {
        b.board[1,2] = p
        b.board[2,2] = p
        b.board[3,2] = p
        b.board[4,2] = p
    }
    or
    {
        b.board[2,2] = p
        b.board[3,2] = p
        b.board[4,2] = p
        b.board[5,2] = p
    }
    or
    {
        b.board[3,2] = p
        b.board[4,2] = p
        b.board[5,2] = p
        b.board[6,2] = p
    }
    or
    {
        b.board[0,3] = p
        b.board[1,3] = p
        b.board[2,3] = p
        b.board[3,3] = p
    }
    or
    {
        b.board[1,3] = p
        b.board[2,3] = p
        b.board[3,3] = p
        b.board[4,3] = p
    }
    or
    {
        b.board[2,3] = p
        b.board[3,3] = p
        b.board[4,3] = p
        b.board[5,3] = p
    }
    or
    {
        b.board[3,3] = p
        b.board[4,3] = p
        b.board[5,3] = p
        b.board[6,3] = p
    }
    or
    {
        b.board[0,4] = p
        b.board[1,4] = p
        b.board[2,4] = p
        b.board[3,4] = p
    }
    or
    {
        b.board[1,4] = p
        b.board[2,4] = p
        b.board[3,4] = p
        b.board[4,4] = p
    }
    or
    {
        b.board[2,4] = p
        b.board[3,4] = p
        b.board[4,4] = p
        b.board[5,4] = p
    }
    or
    {
        b.board[3,4] = p
        b.board[4,4] = p
        b.board[5,4] = p
        b.board[6,4] = p
    }
    or
    {
        b.board[0,5] = p
        b.board[1,5] = p
        b.board[2,5] = p
        b.board[3,5] = p
    }
    or
    {
        b.board[1,5] = p
        b.board[2,5] = p
        b.board[3,5] = p
        b.board[4,5] = p
    }
    or
    {
        b.board[2,5] = p
        b.board[3,5] = p
        b.board[4,5] = p
        b.board[5,5] = p
    }
    or
    {
        b.board[3,5] = p
        b.board[4,5] = p
        b.board[5,5] = p
        b.board[6,5] = p
    }
    or
    {
        b.board[0,6] = p
        b.board[1,6] = p
        b.board[2,6] = p
        b.board[3,6] = p
    }
    or
    {
        b.board[1,6] = p
        b.board[2,6] = p
        b.board[3,6] = p
        b.board[4,6] = p
    }
    or
    {
        b.board[2,6] = p
        b.board[3,6] = p
        b.board[4,6] = p
        b.board[5,6] = p
    }
    or
    {
        b.board[3,6] = p
        b.board[4,6] = p
        b.board[5,6] = p
        b.board[6,6] = p
    }
    or
    //Horizontal
    {
        b.board[0,0] = p
        b.board[0,1] = p
        b.board[0,2] = p
        b.board[0,3] = p
    }
    or
    {
        b.board[0,1] = p
        b.board[0,2] = p
        b.board[0,3] = p
        b.board[0,4] = p
    }
    or
    {
        b.board[0,2] = p
        b.board[0,3] = p
        b.board[0,4] = p
        b.board[0,5] = p
    }
    or
    {
        b.board[0,3] = p
        b.board[0,4] = p
        b.board[0,5] = p
        b.board[0,6] = p
    }
    or
    {
        b.board[1,0] = p
        b.board[1,1] = p
        b.board[1,2] = p
        b.board[1,3] = p
    }
    or
    {
        b.board[1,1] = p
        b.board[1,2] = p
        b.board[1,3] = p
        b.board[1,4] = p
    }
    or
    {
        b.board[1,2] = p
        b.board[1,3] = p
        b.board[1,4] = p
        b.board[1,5] = p
    }
    or
    {
        b.board[1,3] = p
        b.board[1,4] = p
        b.board[1,5] = p
        b.board[1,6] = p
    }
    or
    {
        b.board[2,0] = p
        b.board[2,1] = p
        b.board[2,2] = p
        b.board[2,3] = p
    }
    or
    {
        b.board[2,1] = p
        b.board[2,2] = p
        b.board[2,3] = p
        b.board[2,4] = p
    }
    or
    {
        b.board[2,2] = p
        b.board[2,3] = p
        b.board[2,4] = p
        b.board[2,5] = p
    }
    or
    {
        b.board[2,3] = p
        b.board[2,4] = p
        b.board[2,5] = p
        b.board[2,6] = p
    }
    or
    {
        b.board[3,0] = p
        b.board[3,1] = p
        b.board[3,2] = p
        b.board[3,3] = p
    }
    or
    {
        b.board[3,1] = p
        b.board[3,2] = p
        b.board[3,3] = p
        b.board[3,4] = p
    }
    or
    {
        b.board[3,2] = p
        b.board[3,3] = p
        b.board[3,4] = p
        b.board[3,5] = p
    }
    or
    {
        b.board[3,3] = p
        b.board[3,4] = p
        b.board[3,5] = p
        b.board[3,6] = p
    }
    or
    {
        b.board[4,0] = p
        b.board[4,1] = p
        b.board[4,2] = p
        b.board[4,3] = p
    }
    or
    {
        b.board[4,1] = p
        b.board[4,2] = p
        b.board[4,3] = p
        b.board[4,4] = p
    }
    or
    {
        b.board[4,2] = p
        b.board[4,3] = p
        b.board[4,4] = p
        b.board[4,5] = p
    }
    or
    {
        b.board[4,3] = p
        b.board[4,4] = p
        b.board[4,5] = p
        b.board[4,6] = p
    }
    or
    {
        b.board[5,0] = p
        b.board[5,1] = p
        b.board[5,2] = p
        b.board[5,3] = p
    }
    or
    {
        b.board[5,1] = p
        b.board[5,2] = p
        b.board[5,3] = p
        b.board[5,4] = p
    }
    or
    {
        b.board[5,2] = p
        b.board[5,3] = p
        b.board[5,4] = p
        b.board[5,5] = p
    }
    or
    {
        b.board[5,3] = p
        b.board[5,4] = p
        b.board[5,5] = p
        b.board[5,6] = p
    }
    or
    {
        b.board[6,0] = p
        b.board[6,1] = p
        b.board[6,2] = p
        b.board[6,3] = p
    }
    or
    {
        b.board[6,1] = p
        b.board[6,2] = p
        b.board[6,3] = p
        b.board[6,4] = p
    }
    or
    {
        b.board[6,2] = p
        b.board[6,3] = p
        b.board[6,4] = p
        b.board[6,5] = p
    }
    or
    {
        b.board[6,3] = p
        b.board[6,4] = p
        b.board[6,5] = p
        b.board[6,6] = p
    }
    or
    //Diagnoal
    {
        b.board[0,0] = p
        b.board[1,1] = p
        b.board[2,2] = p
        b.board[3,3] = p
    }
    or
    {
        b.board[1,0] = p
        b.board[2,1] = p
        b.board[3,2] = p
        b.board[4,3] = p
    }
    or
    {
        b.board[2,0] = p
        b.board[3,1] = p
        b.board[4,2] = p
        b.board[5,3] = p
    }
    or
    {
        b.board[3,0] = p
        b.board[4,1] = p
        b.board[5,2] = p
        b.board[6,3] = p
    }
    or
    {
        b.board[0,1] = p
        b.board[1,2] = p
        b.board[2,3] = p
        b.board[3,4] = p
    }
    or
    {
        b.board[1,1] = p
        b.board[2,2] = p
        b.board[3,3] = p
        b.board[4,4] = p
    }
    or
    {
        b.board[2,1] = p
        b.board[3,2] = p
        b.board[4,3] = p
        b.board[5,4] = p
    }
    or
    {
        b.board[3,1] = p
        b.board[4,2] = p
        b.board[5,3] = p
        b.board[6,4] = p
    }
    or
    {
        b.board[0,2] = p
        b.board[1,3] = p
        b.board[2,4] = p
        b.board[3,5] = p
    }
    or
    {
        b.board[1,2] = p
        b.board[2,3] = p
        b.board[3,4] = p
        b.board[4,5] = p
    }
    or
    {
        b.board[2,2] = p
        b.board[3,3] = p
        b.board[4,4] = p
        b.board[5,5] = p
    }
    or
    {
        b.board[3,2] = p
        b.board[4,3] = p
        b.board[5,4] = p
        b.board[6,5] = p
    }
    or
    {
        b.board[0,3] = p
        b.board[1,4] = p
        b.board[2,5] = p
        b.board[3,6] = p
    }
    or
    {
        b.board[1,3] = p
        b.board[2,4] = p
        b.board[3,5] = p
        b.board[4,6] = p
    }
    or
    {
        b.board[2,3] = p
        b.board[3,4] = p
        b.board[4,5] = p
        b.board[5,6] = p
    }
    or
    {
        b.board[3,3] = p
        b.board[4,4] = p
        b.board[5,5] = p
        b.board[6,6] = p
    }
    or
    // Downwards diagonal
    {
        b.board[0,3] = p
        b.board[1,2] = p
        b.board[2,1] = p
        b.board[3,0] = p
    }
    or
    {
        b.board[1,3] = p
        b.board[2,2] = p
        b.board[3,1] = p
        b.board[4,0] = p
    }
    or
    {
        b.board[2,3] = p
        b.board[3,2] = p
        b.board[4,1] = p
        b.board[5,0] = p
    }
    or
    {
        b.board[3,3] = p
        b.board[4,2] = p
        b.board[5,1] = p
        b.board[6,0] = p
    }
    or
    {
        b.board[0,4] = p
        b.board[1,3] = p
        b.board[2,2] = p
        b.board[3,1] = p
    }
    or
    {
        b.board[1,4] = p
        b.board[2,3] = p
        b.board[3,2] = p
        b.board[4,1] = p
    }
    or
    {
        b.board[2,4] = p
        b.board[3,3] = p
        b.board[4,2] = p
        b.board[5,1] = p
    }
    or
    {
        b.board[3,4] = p
        b.board[4,3] = p
        b.board[5,2] = p
        b.board[6,1] = p
    }
    or
    {
        b.board[0,5] = p
        b.board[1,4] = p
        b.board[2,3] = p
        b.board[3,2] = p
    }
    or
    {
        b.board[1,5] = p
        b.board[2,4] = p
        b.board[3,3] = p
        b.board[4,2] = p
    }
    or
    {
        b.board[2,5] = p
        b.board[3,4] = p
        b.board[4,3] = p
        b.board[5,2] = p
    }
    or
    {
        b.board[3,5] = p
        b.board[4,4] = p
        b.board[5,3] = p
        b.board[6,2] = p
    }
    or
    {
        b.board[0,6] = p
        b.board[1,5] = p
        b.board[2,4] = p
        b.board[3,3] = p
    }
    or
    {
        b.board[1,6] = p
        b.board[2,5] = p
        b.board[3,4] = p
        b.board[4,3] = p
    }
    or
    {
        b.board[2,6] = p
        b.board[3,5] = p
        b.board[4,4] = p
        b.board[5,3] = p
    }
    or
    {
        b.board[3,6] = p
        b.board[4,5] = p
        b.board[5,4] = p
        b.board[6,3] = p
    }
    // or
    // wonDUpwards[b, p]
    // or
    // wonDDownwards[b, p]
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

pred doNothing[pre: Board, post: Board, p: Player] {
    // If some player has won


    // Change nothing
    all row: Int, col: Int |
        post.board[row][col] = pre.board[row][col]
}


// Strategy One: Place Column by Column Starting by the Middle 
pred columnsonly[player: Player, row: Int, col: Int, b: Board] {
   
   some b.board[subtract[row, 1]][3] implies (col = 3) 
   
//    else {
//     some row2, col2: Int | {
//         row = row2
//         col = col2
//     }
//    }
  
//    ((col != 4) and (col != 5) and (col != 3)) => (col = 6)
//    ((col != 4) and (col != 5) and (col != 3) and (col != 6)) => (col = 2)
//    ((col != 4) and (col != 5) and (col != 3) and (col != 6) and (col != 2)) => (col = 7)
//    ((col != 4) and (col != 5) and (col != 3) and (col != 6) and (col != 2) and (col != 7)) => (col = 1)

}


// Strategy Two: Place Rows by Row Starting from Left

pred rowsonly[player: Player, row: Int, col: Int, b: Board] {
    row = 0 or one b.board[subtract[row, 1]][col] implies (row = 0)
    row = 0 or one b.board[subtract[row, 1]][col] implies (row = 1)
    row = 0 or one b.board[subtract[row, 1]][col] implies (row = 2)
    row = 0 or one b.board[subtract[row, 1]][col] implies (row = 3)
    row = 0 or one b.board[subtract[row, 1]][col] implies (row = 4)
    row = 0 or one b.board[subtract[row, 1]][col] implies (row = 5)
    row = 0 or one b.board[subtract[row, 1]][col] implies (row = 6)

}

pred traces {
    // Start at initial state
    starting[Game.initialState]

    // All other states are reached by move or doNothing
    all b: Board | some Game.next[b] implies {
        // all p: Player | not won[b, p] => {
        //     some row, col: Int, p2: Player | {
        //         move[b, Game.next[b], row, col, p2]
        //     }
        // }
        // some row, col: Int, p: Player | {
        //     move[b, Game.next[b], row, col, p]          
        // // }
        // some p: Player | won[b, p] => {
        //     doNothing[b, Game.next[b], p]
        // }
        // some p: Player | won[b, p]  =>  {
        //      doNothing[b, Game.next[b], p]
        // } 
        // else {     
         some row, col: Int, p2: Player | {
                p2 = O implies {
                    //columnsonly[p2, row, col, b]
                    not {row = 0}
                    some b.board[subtract[row, 1]][3] implies {col = 3}
                }
                p2 = X implies {
                // first strategy
                // no b.board[0][3] implies (row = 0 and col = 3)
                // (no b.board[1][3] and some b.board[0][3]) implies (col = 3 and row = 1)
                // (no b.board[2][3] and some b.board[0][3] and some b.board[1][3]) implies (col = 3 and row = 2)
                // (row = 0 or one b.board[subtract[row, 1]][3]) implies (col = 3)

                // (row = 0 or one b.board[subtract[row, 1]][3]) implies (col = 2)
                //(row = 0 or one b.board[subtract[row, 1]][col]) implies (row = 0)
                // columnsonly[p2, row, col, b]
                // columnsonly[p2, row, col, b]
                {row = 0 and col = 3} or { {not row = 0} and some b.board[subtract[row, 1]][3] implies {col = 3}}

                }
                move[b, Game.next[b], row, col, p2]
            } 
    }
}



// Example run 
// (see tests for more, particularly test expects that check winning) – this 
// run is really just for demonstration, and it's possible that no one wins yet
// with 10 Board. We show that someone will win eventually in testing.
pred strategyone[b: board, g: Game] {
    // defensive strategy
    // follow whatever the opponent does and calculate how many 

    // Choose the center column. This column gives you the most options for 
    // connecting four of your pieces in a row.
   some row : Int | no b.board[row][3] => {
       move[b,  Game.next[b], row, 3, X] or move[b,  Game.next[b], row, 3, O]
    }

}


run {
    allWellformed
    traces 
} for 1 Game, 12 Board for {next is linear}



// run {
//     allWellformed
//     traces and strategyone[Board]
// } for 20 Board for {next is linear}


