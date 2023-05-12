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
        (row < 0 or row > 5 or col < 0 or col > 6) implies {
            no b.board[row][col]
        }
    }
}

// Packages wellformed into a pred applying to all Boards, for ease of reference
pred allWellformed {
    all b: Board{
        wellformed[b]
    }
}

//Checks that boards are valid
pred allValidBoard {
    all b: Board {
        {#{row, col: Int | b.board[row][col] = X} = #{row, col: Int | b.board[row][col] = O}}
        or
        {#{row, col: Int | b.board[row][col] = X} = add[#{row, col: Int | b.board[row][col] = O}, 1]}
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
pred won[b: Board] {
    // wonH[b, p]
    // or
    // wonV[b, p]
    // or
    some p: Player | 
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
    // won[pre, p]

    // Change nothing
    all row: Int, col: Int |
        post.board[row][col] = pre.board[row][col]
}

pred traces {
    // Start at initial state
    starting[Game.initialState]

    // All other states are reached by move or doNothing
    // all b: Board | some Game.next[b] implies {
        
    //     won[b] => {
    //         doNothing[b, Game.next[b]]
    //     } else {
    //         some row, col: Int, p: Player | {
    //             move[b, Game.next[b], row, col, p]
    //         }
    //     }

    // }


    // Strategy 1
    // Black prioritizes placing tokens in spots that would already have black tokens adjacent or diagonal.
    // Red simply prioritizes building upwards by never going in row zero

    // all b: Board | some Game.next[b] implies {
    //     won[b] => {
    //         doNothing[b, Game.next[b]]
    //     } else {    
    //      some row, col: Int, p: Player | {
    //             p = O implies {
    //                 {
    //                     not {row = 0}
    //                     some b.board[subtract[row, 1]][col]
    //                 }

    //             }
    //             p = X implies {
    //                 {
    //                     row = 0
    //                 }
    //                 or
    //                 {
    //                     row = 0
    //                     some b.board[row][subtract[col, 1]]
    //                     b.board[row][subtract[col, 1]] = p
    //                 }
    //                 or
    //                 {
    //                     {not row = 0}
    //                     {
    //                         {
    //                             some b.board[subtract[row, 1]][col]
    //                             b.board[subtract[row, 1]][col] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[row][subtract[col, 1]]
    //                             b.board[row][subtract[col, 1]] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[subtract[row, 1]][subtract[col, 1]]
    //                             b.board[row][subtract[col, 1]] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[subtract[row, 1]][add[col, 1]]
    //                             b.board[row][add[col, 1]] = p
    //                         }
    //                     }
    //                 }
    //             }
    //             move[b, Game.next[b], row, col, p]
    //         }
    //     }
    // }

    // Strategy 2
    // Black prioritizes placing tokens in spots that would already have black tokens adjacent or diagonal.
    // Red plays a naive defensive strategy only placing tokens adjacent to existing black tokens, trying to "block" black from forming streaks.

    // all b: Board | some Game.next[b] implies {
    //     won[b] => {
    //         doNothing[b, Game.next[b]]
    //     } else {    
    //      some row, col: Int, p: Player | {
    //             p = O implies {
    //                 {
    //                     not {row = 0}
    //                     some b.board[subtract[row, 1]][col]
    //                     not b.board[subtract[row, 1]][col] = p
    //                 }
    //                 or
    //                 {
    //                     {row = 0}
    //                     some b.board[row][subtract[col, 1]]
    //                     not b.board[row][subtract[col, 1]] = p
    //                 }
    //                 or
    //                 {
    //                     {row = 0}
    //                     some b.board[row][add[col, 1]]
    //                     not b.board[row][add[col, 1]] = p
    //                 }
    //                 or
    //                 {
    //                     not {row = 0}
    //                     some b.board[subtract[row, 1]][subtract[col, 1]]
    //                     not b.board[subtract[row, 1]][subtract[col, 1]] = p
    //                 }
    //                 or
    //                 {
    //                     not {row = 0}
    //                     some b.board[subtract[row, 1]][add[col, 1]]
    //                     not b.board[subtract[row, 1]][add[col, 1]] = p
    //                 }

    //             }
    //             p = X implies {
    //                 {
    //                     row = 0
    //                 }
    //                 or
    //                 {
    //                     row = 0
    //                     some b.board[row][subtract[col, 1]]
    //                     b.board[row][subtract[col, 1]] = p
    //                 }
    //                 or
    //                 {
    //                     {not row = 0}
    //                     {
    //                         {
    //                             some b.board[subtract[row, 1]][col]
    //                             b.board[subtract[row, 1]][col] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[row][subtract[col, 1]]
    //                             b.board[row][subtract[col, 1]] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[subtract[row, 1]][subtract[col, 1]]
    //                             b.board[row][subtract[col, 1]] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[subtract[row, 1]][add[col, 1]]
    //                             b.board[row][add[col, 1]] = p
    //                         }
                            
    //                     }
                        

    //                 }
    //             }
    //             move[b, Game.next[b], row, col, p]
    //         }
    //     }
    // }

    // // Strategy 3
    // all b: Board | some Game.next[b] implies {
    //     won[b] => {
    //         doNothing[b, Game.next[b]]
    //     } else {    
    //      some row, col: Int, p: Player | {
	// 		    p = O implies {
    //                 {
    //                     not {row = 0}
    //                     some b.board[subtract[row, 1]][col]
    //                     not b.board[subtract[row, 1]][col] = p
    //                 }
    //                 or
    //                 {
    //                     {row = 0}
    //                     some b.board[row][subtract[col, 1]]
    //                     not b.board[row][subtract[col, 1]] = p
    //                 }
    //                 or
    //                 {
    //                     {row = 0}
    //                     some b.board[row][add[col, 1]]
    //                     not b.board[row][add[col, 1]] = p
    //                 }
    //                 or
    //                 {
    //                     not {row = 0}
    //                     some b.board[subtract[row, 1]][subtract[col, 1]]
    //                     not b.board[subtract[row, 1]][subtract[col, 1]] = p
    //                 }
    //                 or
    //                 {
    //                     not {row = 0}
    //                     some b.board[subtract[row, 1]][add[col, 1]]
    //                     not b.board[subtract[row, 1]][add[col, 1]] = p
    //                 }

    //             }
    //             p = X implies {
    //                 {
    //                     col = 3
    //                 }
    //                 or
    //                 {
    //                     {not col = 3}
    //                     {
    //                         {
    //                             some b.board[row][subtract[col, 1]]
    //                             b.board[row][subtract[col, 1]] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[row][add[col, 1]]
    //                             b.board[row][add[col, 1]] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[subtract[row, 1]][subtract[col, 1]]
    //                             b.board[row][subtract[col, 1]] = p
    //                         }
    //                         or
    //                         {
    //                             some b.board[subtract[row, 1]][add[col, 1]]
    //                             b.board[row][add[col, 1]] = p
    //                         }
    //                     }
    //                 }
    //             }
    //             move[b, Game.next[b], row, col, p]
    //         }
    //     }
    // }

    // Strategy 4

    all b: Board | some Game.next[b] implies {
        won[b] => {
            doNothing[b, Game.next[b]]
        } else {    
         some row, col: Int, p: Player | {
			    // p = O implies {
                //     {
                //         not {row = 0}
                //         some b.board[subtract[row, 1]][col]
                //         not b.board[subtract[row, 1]][col] = p
                //     }
                //     or
                //     {
                //         {row = 0}
                //         some b.board[row][subtract[col, 1]]
                //         not b.board[row][subtract[col, 1]] = p
                //     }
                //     or
                //     {
                //         {row = 0}
                //         some b.board[row][add[col, 1]]
                //         not b.board[row][add[col, 1]] = p
                //     }
                //     or
                //     {
                //         not {row = 0}
                //         some b.board[subtract[row, 1]][subtract[col, 1]]
                //         not b.board[subtract[row, 1]][subtract[col, 1]] = p
                //     }
                //     or
                //     {
                //         not {row = 0}
                //         some b.board[subtract[row, 1]][add[col, 1]]
                //         not b.board[subtract[row, 1]][add[col, 1]] = p
                //     }

                // }
                p = X implies {
                    {
                        {
                            no b.board[row][subtract[col, 1]]
                            no b.board[row][add[col, 1]]
                            no b.board[subtract[row, 1]][subtract[col, 1]]
                            no b.board[subtract[row, 1]][add[col, 1]]
                            // not b.board[row][subtract[col, 1]] = p
                        }
                        or
                        {
							{
								some b.board[row][subtract[col, 1]] or 
								some b.board[row][add[col, 1]] or
								some b.board[subtract[row, 1]][subtract[col, 1]] or
								some b.board[subtract[row, 1]][add[col, 1]] 
							} implies {
								not b.board[row][subtract[col, 1]] = p and
								not b.board[row][add[col, 1]] = p and
								not b.board[subtract[row, 1]][subtract[col, 1]] = p and 
								not b.board[subtract[row, 1]][add[col, 1]] = p
							}
                        }
                    }
                }
                move[b, Game.next[b], row, col, p]
            }
        }
    }


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

// Example run 
// (see tests for more, particularly test expects that check winning) – this 
// run is really just for demonstration, and it's possible that no one wins yet
// with 10 Board. We show that someone will win eventually in testing.
// run {
//     allWellformed
//     traces
// } for 20 Board for {next is linear}


// TODO: Check that it is possible to win
// TODO: Check that it is possible to draw / not win in the number of boards in the trace
// TODO: Check validMoves -- DONE

test expect {
    validMoves: {
        allWellformed
        allValidBoard
        traces
    } for 43 Board for {next is linear} is unsat
}
