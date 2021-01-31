
(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Impl

open Absyn
open Prelude
open System
open System.Runtime.Remoting.Metadata.W3cXsd2001


// RATIONALIZE
// La funzione rationalize converte un elemento di tipo float in un elemento di tipo rational
// Per fare questo trasforma l'elemento in una stringa e divide la parte intera da quella decimale
// poi unisce le due stringhe e le converte in intero per ottenere il nominatore e eleva 10. alla
// lunghezza della stringa della parte decimale per ottenere il denominatore, infine restituisce
// rational della coppia (numeratore, denominatore)

let rationalize (x : float) : rational =
    let s = sprintf "%f" x
    let s_array = s.Split [|'.'|]
    let interi = s_array.[0]
    let decimali = s_array.[1]
    let valore = interi + decimali
    let numeratore = Int32.Parse valore
    let denominatore = int (10. ** (float decimali.Length))
    in rational (numeratore, denominatore)
  
//  MONOMIAL_DEGREE
// La funzione monomial_degree prende in input un monomio e restituisce il grado del monomio

let monomial_degree (m : monomial) : int =
    match m with
    | Monomial (x, n) -> n

// MONOMAL_NEGATE
// La funzione monomial_negate prende in input un monomio e restituisce il monomio negato, applicando un - davanti al coefficiente

let monomial_negate (m : monomial) : monomial =
    match m with
    | Monomial (x, n) -> Monomial (-x, n)

// POLYNOMIAL_DEGREE
// La funzione polynomial_degree è una funzione ricorsiva che prende in input un polinomio e restituisce
// il grado maggiore dei monomi che compongono il polinomio.

let rec polynomial_degree (p : polynomial) : int =
    match p with
    | Polynomial []      -> 0
    | Polynomial (x::xs) -> if (monomial_degree x) > (polynomial_degree (Polynomial xs))
                                then monomial_degree x
                            else polynomial_degree (Polynomial xs)

// POLYNOMMIAL_NEGATE
// La funzione polynomial_negate prende un polinommio e nega il polinomio
// Si appoggia alla funzione aux_poly_negate:
//     • prende un polinomio e restituisce il polinomio con tutti i monomi negati

let rec aux_poly_negate (p : polynomial) : monomial list =
    match p with
    | Polynomial []      -> []
    | Polynomial (x::xs) -> (monomial_negate x) :: (aux_poly_negate (Polynomial xs))

let polynomial_negate (p : polynomial) : polynomial = Polynomial (aux_poly_negate p)

// NORMALIZE
// La funzione normalize si appoggia a tre funzioni ausiliarie:
//     • coefficienti che prende una lista di monomi e un grado e restituisce la somma dei coefficienti
//                    dei diversi monomi della lista che presentano quel grado
//     • rtn_lst che prende una lista di monomi e un grado (che viene incrementato ad ogni ricorsione) e
//               ritorna una lista di razionali, ovvero una lista dei coefficienti dei monomi ricavati da
//               coefficienti e messi in ordine di grado. Notare che se un certo grado non compare mai in
//               nessun monomio la funzione coefficienti ritornerà uno 0Q
//     • aux_normalize che dato un polinomio, restituisce un array di razionali trasformando la lista di
//                     razionali che prende da rtn_lst
// Stabilite le funzioni ausiliarie, normalize usa due cicli while:
//     • il primo stabilisce qual è la posizione dell'ultimo elemento dell'array di aux_normalize diverso da 0Q
//     • il secondo costruisce un nuovo array uguale all'array di aux_normalize fino all'ultimo elemento
//       diverso da 0Q e lo trasforma in un normalized_polynomial

let rec coefficienti (ml : monomial list) (degree : int) : rational =
    match ml with
    | [] -> 0Q
    | (Monomial (c, n))::xs -> if n = degree
                                   then c + (coefficienti xs degree)
                               else coefficienti xs degree

let rec rtn_lst (ml : monomial list) (degree : int) : rational list =
    match polynomial_degree (Polynomial ml) with
    | d when d < degree -> []
    | _ -> (coefficienti ml degree) :: (rtn_lst ml (degree + 1))

let aux_normalize (Polynomial p : polynomial) : rational array = List.toArray ((rtn_lst p 0))

let normalize (p : polynomial) : normalized_polynomial =
    let mutable i = (Array.length (aux_normalize p) - 1)
    let mutable flag = false

    while i > 0 && flag = false do
        if (aux_normalize p).[i] = 0Q
            then i <- i - 1
        else flag <- true

    let arr = Array.init (i + 1) (fun _ ->  0Q)
    let mutable j = 0

    while j <= i do
        arr.[j] <- ((aux_normalize p).[j])
        j <- j + 1
    NormalizedPolynomial arr

// NORMALIZE_POLYNOMIAL_DEGREE
// La funzione normalize_polynomial_degree calcola il grado di un polinomio normalizzato
// Per calcolare il grado del polinomio normalizzato calcoliamo la lunghezza dell'array di cui è composto
// normalized_polynomial e sottraiamo 1

let normalized_polynomial_degree (np : normalized_polynomial) : int =
    match np with
    | NormalizedPolynomial arr -> (Array.length arr) - 1

// DERIVE
// La funzione derive calcola la derivata di un polinomio appoggiandosi alla funzione ausiliaria aux_derive:
//     • aux_derive scompatta la lista di monomi del polinomio e per ogni monomio moltiplica il coefficiente
//       per il razionale del grado e sottae 1 al grado

let rec aux_derive (p : polynomial) : monomial list =
    match p with
    | Polynomial []                      -> []
    | Polynomial [Monomial (x, n)]       -> [Monomial (x * (rational n), n - 1)]
    | Polynomial ((Monomial (x, n))::xs) -> (Monomial (x * (rational n), n - 1)) :: (aux_derive (Polynomial xs))

let derive (p : polynomial) : polynomial = Polynomial (aux_derive p)

// REDUCE e EQUAZIONE
// La funzione reduce stabilisce se un expr è:
//     • un Poly of polinomial e in questo caso restituisce il polinomio
//     • un Derive of expr e in questo caso deriva expr appoggiandosi alla funzione derive
// La funzione equazione prende un coppia di expr si appoggia alla funzione ausiliaria aux_equazione:
//    • aux_equazione utilizza reduce per verificare se i due expr sono da derivare o meno e restituisce due polinomi
// per restituire un polinomio ricavato dall'unione delle liste di monomi dei polinomi di aux_equazione

let rec reduce (e : expr) : polynomial =
    match e with
    | Poly p   -> p
    | Derive d -> derive (reduce d)

let aux_equazione ((e1, e2) : expr * expr) : polynomial * polynomial = 
    match (reduce e1, reduce e2) with
    | (p1, p2) -> (p1, (polynomial_negate p2))

let equazione ((e1, e2) : expr * expr) : polynomial= 
    match (aux_equazione (e1, e2)) with
    | ((Polynomial m1), (Polynomial m2)) -> Polynomial (m1 @ m2)

// SOLVE0
// La funzione Solve0 verifica se l'identità ottenuta è vera.
// Compara il valore ottenuto dalla normalizzazione dell'equazione data in input al secondo membro, ovvero 0.
// Lo zero viene rappresentato sotto forma di polinomio normalizzato contenente un solo monomio di grado e coefficiente 0.
// Se l'identità risulta vera, viene restituito il valore booleano true;
// in caso contrario, viene restituito il valore booleano false.

let solve0 (np : normalized_polynomial) : bool = np = (normalize (Polynomial [Monomial (0Q, 0)]))

// SOLVE1
// La funzione Solve1 restituisce semplicemente la soluzione dell'equazione di primo grado:
// viene fornito in input un polinomio normalizzato, che corrisponde al primo membro dell'equazione.
// Il polinomio è formato solamente da due monomi, uno dei quali (quello di grado 0, cioè senza la x)
// viene cambiato di segno come se fosse portato a destra dell'uguale.
// Divido il coefficiente di tale monomio per il coefficiente del monomio di grado 1.
// Infine la formula di risoluzione diventa -a / b

let solve1 (np : normalized_polynomial) : rational =
    match np with
    | NormalizedPolynomial [|a; b|] -> (-a) / b

// SOLVE2  
// La funzione Δ ricava l'omonimo valore dall'equazione generale dell'equazione di secondo grado a(x)**2 + bx + c.
// Tale equazione gli viene data in input attraverso l'array del polinomio normalizzato,
// e come output restituisce un valore float.
// Solve2 si occupa di applicare la formula per trovare le soluzioni di un'equazione di secondo grado
// a seconda del valore di Δ, più precisamente:
// 	   • nel caso di Δ negativo, le soluzioni non ci sono in quanto non presenti nell'insieme dei numeri razionali;
// 	   • nel caso di Δ = 0, le soluzioni coincideranno, quindi viene restituita un'unica soluzione, ricavata dalla formula -b / 2a
// 	   • nel caso di Δ positivo, le soluzioni sono due e vengono restituite entrambe, ricavate dalla formula (-b ± (sqrt Δ)) / 2a

let delta (a : rational array) : float =  float ((a.[1]) ** 2 - ( 4Q * (a.[0]) * (a.[2])))

let solve2 (NormalizedPolynomial np : normalized_polynomial) : (float * float option) option =
    let c = (float np.[0])
    let b = (float np.[1])
    let a = (float np.[2])

    if (delta np) < 0.
        then None
    else if (delta np) = 0.
            then Some ((-b / (2. * a)), None)
    else Some (((-b + (sqrt (delta np))) / (2. * a)), Some ((-b - (sqrt (delta np))) / (2. * a)))