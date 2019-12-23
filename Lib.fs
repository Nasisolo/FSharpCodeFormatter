/// Modulo contenente funzioni utili all'implementazione del progetto.
module Lib

// È FORTEMENTE CONSIGLIATO L'UTILIZZO DELLE FUNZIONI QUI CONTENUTE: LE FUNZIONI SEGUENTI SONO PENSATE
// PER AIUTARVI NELL'IMPLEMENTAZIONE E PER DARVI QUALCHE SPUNTO SULLE STRUTTURE DATI DA UTILIZZARE.

open System

let tab_size = 4
let tabulate n = new string (' ', n * tab_size)

/// Elimina spazi, tabulazioni e caratteri di end-of-line all'inizio e alla fine di una stringa.
let trim_line (s : string) = s.Trim [|' '; '\t'; '\r'; '\n'|]

/// Spezza una stringa in singole parole separate da white space (cioè spazi e/o tabulazioni).
let tokenize_line (s : string) = s.Split ([|' '; '\t'|], StringSplitOptions.RemoveEmptyEntries) |> List.ofArray

/// Spezza una stringa in linee utilizzando come separatore il carattere di end-of-line. Tale carattere è multi-piattaforma, cioè si adegua automaticamente
/// ai diversi sistemi operativi.
let split_lines (s : string) = s.Split ([|Environment.NewLine|], StringSplitOptions.None) |> Array.map trim_line |> List.ofArray

/// Funzione di debug che stampa una lista di coppie int * string. Ogni elemento della lista rappresenta una linea di codice tabulato: l'intero è il valore
/// della tabulazione e la stringa il testo.
let print_tabbed_lines tlines =
    printfn "\n------------DEBUG-----------\n"
    for tabn, line in tlines do
        printfn "%2d, \"%s\"" tabn line

/// Funzione di appoggio per le due successive.
let private split_line toklen (tok : string) (line : string) =
    let i = line.IndexOf tok + toklen
    in
        trim_line (line.Substring (0, i)), trim_line (line.Substring (i, line.Length - i))

/// Chiamare split_line_in tok line divide l'argomento line usando la prima occorrenza tok come pivot. Il risultato è una coppia di stringhe: la parte prima di tok e
/// la parte dopo tok. La stringa tok è inclusa nella prima parte.
let split_line_inc (tok : string) = split_line tok.Length tok

/// Chiamare split_line_in tok line divide l'argomento line usando la prima occorrenza tok come pivot. Il risultato è una coppia di stringhe: la parte prima di tok e
/// la parte dopo tok. La stringa tok è inclusa nella seconda parte.
let split_line_exc = split_line 0

/// Produce una stringa data una lista di coppie int * string che rappresentano una linea tabulata del sorgente di output.
let render tlines =
    #if DEBUG
    print_tabbed_lines tlines
    #endif
    let rec R l =
        match l with
        | [] -> ""
        | (n, line) :: xs ->
            let tab = tabulate n
            in
                tab + line + "\n" + R xs
    R tlines
