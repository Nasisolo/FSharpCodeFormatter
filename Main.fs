
module FSharpCodeFormatter.Main

open System
open Lib

/// La chiamata format w s produce una stringa col programma formattato correttamente dati un intero w, che rapprenseta la lunghezza massima di ogni linea,
/// e la stringa s con l'input. Implementa in pratica l'intera catena di funzioni che trasformano l'input nell'output.
let format w s = render (Formatter.indent (Formatter.split w s))


[<EntryPoint>]
let main _ = 
    let width = 10          // cambia questo per provare width diverse
    let input = Test.all // puoi cambiare i sorgenti di test per provare input diversi
    printfn "------------INPUT------------\n%s" input
    let output = format width input
    printfn "\n------------OUTPUT------------\n%s" output
    #if DEBUG
    ignore <| Console.ReadKey ()
    #endif
    0
