#load "../Dawg/Dawg.fs"
open Dawg

module SG = Graph

/// Finds all occurences of the given word in the given graph. Returns the list of all end positions
/// of a word in a text corrsponding given subword graph.
let findOccurences (w:string) (g:SG.Dawg<char>) =
    let g' = SG.insert g '#'
    let t = SG.toWord g'
    let m = Seq.length t

    match SG.findNode w g' with
        | None -> []
        | Some n ->
            let f (_, (dst, _)) st1 st2 =
                if dst = g'.SinkId
                    then [1]
                    else st1 @ List.map ((+) 1) st2

            let l = SG.foldBackFromNode f [] g' n
            List.map (fun x -> m - x) <| fst l 

/// Counts how many times does the given word occur in the given graph.
let countRepeats (w:string) (g: SG.Dawg<char>) =
    let g' = SG.insert g '#'

    match SG.findNode w g' with
        | None -> 0
        | Some n ->
            let f (_, (dst, _)) st1 st2 =
                if dst = g'.SinkId
                    then 1 + st1
                    else st1 + st2

            SG.foldBackFromNode f 0 g' n |> fst

/// Returns the list of all suffixes present in a given subword graph. The ordering is as in a suffix array.
let suffixes (g: SG.Dawg<char>) =
    let endmarker = '#'
    let g' = SG.insert g endmarker
    let f (c, (dst, _)) s1 s2 =
        if dst = g'.SinkId
            then s1 @ [[c]]
            else s1 @ List.map (fun l -> c::l) s2
    
    SG.foldBack f [] g' |> List.tail
