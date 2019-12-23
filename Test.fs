module FSharpCodeFormatter.Test

module Basic =
    let prg1 = """
    let f x =
    if x > 0 then 1
    else
    let y = x + 2
    let f x =
    if x > 0 then
    let a = 1
    in a + b
    elif x > 0 then 3
    else
    let a = 1
    in a
    in f y + f z
    """

    let prg2 = """
    let f x =
    match a with
    | 1 -> 
    match b with
    | 2 -> 2
    | 3 ->
    match c with
    | 4 -> 4
    | 5 -> 5
    """


    let prg3 = """
    let rec F y =
    let f x = x + 1
    let y = f 4
    match f 3 with
    | 2 ->
    match y with
        | 3 -> true
    | 4 ->
    if p 3 then 
    let z = 8
    in z < y
    else false
    """

    let prg4 = """
    let f x =
    let res = 
    match x with
    | 0 -> 1
    | 1 -> 18
    | 2 ->
    match x + 45 with
    | 47 -> x * 2
    | _ -> 7
    in res + 8
    """
    let prg5 = """
    let f x =
    let res =
    if x < 5 then
    let a = 8
    let b =
    if x < 3 then 8
    else 3
    in x + a * b
    else
    let c =
    match x with
    | 6 -> 7
    | _ -> 78    
    let d = 1
    in x * c + d
    in res
    """

module Advanced =
    let prg1 = """
    let funzione x = if x > 0 then 3 else funzione 2
    """

    let prg2 = """
    let rec foldl f z l = match l with | [] -> if x > 0 then 1 else 3 | x :: xs -> foldl f (f z x) xs
    """

    let prg3 = """
    let rec map f l = let k = 1 let rec R c = match c with | [] -> [] | x :: xs -> match f x with | [] -> 3 | x :: xs -> match a with | [] -> [] | x :: xs -> 3 in R [] 
    """


module A = Advanced
module B = Basic

let flatten = List.fold (+) ""

let basic = [B.prg1; B.prg2; B.prg3; B.prg4; B.prg5] |> flatten 

let advanced = [A.prg1; A.prg2; A.prg3] |> flatten 

let all = basic + advanced


