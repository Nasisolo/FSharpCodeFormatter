module FSharpCodeFormatter.Formatter

open Lib
open System.Security.Cryptography.X509Certificates

// se non vuoi realizzare la versione avanzata, non modificarla
let split (w : int) (s : string) = split_lines s




//----------------------------------------funzioni ausiliarie------------------------------------

/// Funzione ausiliara di supporto per eseguire la funzione "last", restituisce la lista rovesciata
let rec reverse l =
    match l with
    |[]     -> []
    |x::xs  -> reverse xs@[x]

/// Funzione che data una lista, restituisce il primo elemento di essa
let first l =
    match l with
    |[x] -> x
    |x::xs -> x

/// Funzione che data una lista restituisce l'ultimo elemento di una lista di tipo 'a,
/// l'ultimo elemento equivale al primo elemento della lista rovesciata
let last l = first (reverse l)

/// Verifica se la stringa "else" ha in coda una lista vuota (true) o una lista con elementi (false),
/// si può comprendere così se l'else in questione è monoriga
let singleElse tail =
    match reverse tail with
    |[] -> true
    |x::xs -> false

/// Funzione che data una lista, restituisce la lista meno l'ultimo elemento
let rec remove_last l =
    match l with
    |[] -> []
    |[x]    -> []    //questo patternmatching canncella l'ultimo elemento
    |x::xs  -> x::remove_last xs



//---------------------------------------controllo costrutti------------------------------------------

let rec check lines glob prev_line last_if last_let last_match=
    match  lines with   // prende la prima riga della lista che viene passata
    |[]     -> []
    |s::ss  ->  match tokenize_line(trim_line s) with   // prende il primo valore di ogni riga e fa il patternamtching dei vari costrutti
                |[]     ->  (0,s) :: check ss 0 prev_line last_if last_let last_match
                |x::xs  ->  match x with
                                        // let a top level
                                        // se finisce con "=" e la riga precedente è vuota, la riga successiva avrà tabulazione +1 (glob+1) e verranno passati tutti gli altri valori
                                        // dopo la prima volta che viene trovato il let a top level, verrà sempre passato [s] nella riga precedente per non rientrare nuovamente in questo match
                            |"let"  ->  if last xs = "=" && prev_line = [] then (glob, s) :: check ss (glob+1) [s] last_if last_let last_match
                                        // let locale che finisce con "="
                                        // la riga successiva sarà tabulata +1 e la tab. di questa riga verrà salvata in una lista la tabulazione di let (last_let@[glob])
                                        elif last xs = "=" && prev_line <> [] then (glob, s) :: check ss (glob+1) [s] last_if (last_let@[glob]) last_match
                                        // let successivo ad una riga che inizia con "|"
                                        // la riga avrà stessa tabulazione dell'ultimo let "top level" e passerà la lista dei let meno l'ultimo elemento che stato appena usato e la tabulazione globale
                                        elif first(tokenize_line(first prev_line)) = "|" then (last last_let, s) :: check ss (glob) [s] last_if (remove_last last_let) last_match
                                        // let locale che finisce con una espressione
                                        // restituisce la coppia (tabulazioni_globali, stringa) passando +0 tabulazioni per la riga successiva e salvando la posizione di tab. di questo let in una lista
                                        else (glob, s) :: check ss glob [s] last_if  (last_let@[glob]) last_match
                                        
                                        // costrutto if
                                        // se la riga finisce con "then", allora si tabula di uno per l'espressione nella riga successiva e si salva la tab. in una lista last_if
                            |"if"   ->  if last xs = "then" then (glob,s) :: check ss (glob+1) [s] (last_if@[glob]) last_let last_match
                                        // se la riga contiene un'espressione dopo il then allora la riga successiva NON verrà tabulata di +1 e si salva la tab. nella lista last_if
                                        else (glob,s) :: check ss glob [s] (last_if@[glob]) last_let last_match
                                        
                                        // costrutto elif
                                        // funziona come il costrutto if, solo che restituisce la coppia (ultima_tabulazione_if, stringa)
                                        // primo caso: la riga finisce con "then" e tabula di +1 la riga successiva passando la posizione precedente del last_if
                            |"elif" ->  if last xs = "then" then (last last_if,s) :: check ss (glob+1) [s] last_if last_let last_match
                                        // secondo caso: la riga finisce con un'espressione e NON viene tabulata di +1 la riga successiva per mettere l'espressione nella stessa colonna dell'elif
                                        else (last last_if,s) :: check ss glob [s] (last_if) last_let last_match
                                        
                                        // costrutto else
                                        // verfica se "else" è monoriga, in questo caso si restituisce la posizione dell'ultimo if e si tabula di +1 per la riga successiva
                                        // in quanto chiude la sequenza if/elif/else, si rimuove l'ultimo elemento della lista last_if con (remove_last last:if)
                            |"else" ->  if singleElse xs = true then (last last_if, s) :: check ss ((last last_if)+1) [s] (remove_last last_if) last_let last_match
                                        // se il costrutto "else" ha nella stessa riga un'espressione, allora si restituisce la pos. dell'ultimo if e la stringa
                                        // viene passato lo stesso numero di tabulazioni globali e si rumuove l'ultima posizione dal last_if
                                        else (last last_if,s) :: check ss glob [s] (remove_last last_if) last_let last_match
                           
                                        // costrutto match
                                        // in quanto finisce con with, le tabulazioni dei pattern saranno dello stesso valore che verrà salvato nella lista last_match
                            |"match"->  (glob, s) :: check ss glob [s] last_if last_let (last_match@[glob])

                                        // pattern
                                        // si restituisce la coppia (ultima_tabulazione_match, stringa)
                                        // se un pattern finisce con "->", allora si tabula di +1
                            |"|"    ->  if last xs = "->" then (last last_match, s) :: check ss (glob+1) [s] last_if last_let last_match
                                        // se un pattern contiene l'espressione alla fine, allora la riga successiva sarà sempre nella stessa colonna dell'ultimo match
                                        else (last last_match , s) :: check ss glob [s] last_if last_let last_match
                                        
                                        // non è un costrutto
                                        // viene restituita nella stessa posizione dell'ultimo let che finisce con un "=" o con un let di cui la riga successiva conterrà un "in"
                                        // in quanto chiude il costrutto "let", rimuove l'ultima posizione del let salvata nella lista last_let durante la ricorsione in coda
                            |"in"   ->  (last last_let, s) :: check ss (glob) [s] last_if (remove_last last_let) last_match
                                        
                                        // lamda astrazioni
                                        // primo caso: se la riga finisce con "->", allora la riga dopo avrà tabulazione +1 rispetto a questa riga
                            |"fun"  ->  if last xs = "->" then (glob, s) ::  check ss (glob+1) [s] last_if last_let last_match
                                        //secondo caso: la riga finisc econ una espressione e quindi la riga successiva sarà incolonnata a questa
                                        else (glob, s) ::  check ss glob [s] last_if last_let last_match

                                        // qualsiasi altra espressione non avente costrutti iniziali
                            |_      ->  (glob, s) :: check ss glob prev_line last_if last_let last_match
                            

                

// questa è la funzione principale da implementare correttamente sia per versione avanzata che per quella normale
let indent (lines : string list) = check lines 0 [] [] [0] [0]

