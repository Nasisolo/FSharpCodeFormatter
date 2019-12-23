module FSharpCodeFormatter.Formatter

/// La chiamata split w s divide la stringa di input s in linee usando il carattere di end-of-line.
/// Il parametro w rappresenta la lunghezza massima di ogni singola linea.
val split : (int -> string -> string list)

/// Data una lista di stringhe che rappresentano le diverse linee del sorgente di input, produce una lista di coppie int * string dove il primo elemento
/// è il valore della tabulazione ed il secondo la linea di codice.
val indent : (string list -> (int * string) list)
