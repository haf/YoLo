[<AutoOpen>]
module internal YoLo

open System

let curry f a b = f (a, b)

let uncurry f (a, b) = f a b

let flip f a b = f b a

module Choice =

  let create v = Choice1Of2 v

  let createSnd v = Choice2Of2 v

  let map f = function
    | Choice1Of2 v -> Choice1Of2 (f v)
    | Choice2Of2 msg -> Choice2Of2 msg

  let mapSnd f = function
    | Choice1Of2 v -> Choice1Of2 v
    | Choice2Of2 v -> Choice2Of2 (f v)

  let bind (f : 'a -> Choice<'b, 'c>) (v : Choice<'a, 'c>) =
    match v with
    | Choice1Of2 v -> f v
    | Choice2Of2 c -> Choice2Of2 c

  let bindSnd (f : 'a -> Choice<'c, 'b>) (v : Choice<'c, 'a>) =
    match v with
    | Choice1Of2 x -> Choice1Of2 x
    | Choice2Of2 x -> f x

  let apply f v =
    bind (fun f' ->
      bind (fun v' ->
        create (f' v')) v) f

  let applySnd f v =
    bind (fun f' ->
      bindSnd (fun v' ->
        createSnd (f' v')) v) f

  let lift2 f v1 v2 =
    apply (apply (create f) v1) v2

  let lift3 f v1 v2 v3 =
    apply (apply (apply (create f) v1) v2) v3

  let lift4 f v1 v2 v3 v4 =
    apply (apply (apply (apply (create f) v1) v2) v3) v4

  let lift5 f v1 v2 v3 v4 v5 =
    apply (apply (apply (apply (apply (create f) v1) v2) v3) v4) v5

  let ofOption onMissing = function
    | Some x -> Choice1Of2 x
    | None   -> Choice2Of2 onMissing

  let inject f = function
    | Choice1Of2 x -> f x; Choice1Of2 x
    | Choice2Of2 x -> Choice1Of2 x

  let injectSnd f = function
    | Choice1Of2 x -> Choice1Of2 x
    | Choice2Of2 x -> f x; Choice1Of2 x

  module Operators =

    let inline (>>=) m f =
      bind f m

    let inline (>>-) m f = // snd
      bindSnd f m

    let inline (=<<) f m =
      bind f m

    let inline (-<<) f m = // snd
      bindSnd f m

    let inline (>>*) m f =
      inject f m

    let inline (>>@) m f = // snd
      injectSnd f m

    let inline (<*>) f m =
      apply f m

    let inline (<!>) f m =
      map f m

    let inline (>!>) m f =
      map f m

    let inline (<@>) f m = // snd
      mapSnd f m

    let inline (>@>) m f = // snd
      mapSnd f m

    let inline ( *>) m1 m2 =
      lift2 (fun _ x -> x) m1 m2

    let inline ( <*) m1 m2 =
      lift2 (fun x _ -> x) m1 m2


module Option =

  let create x = Some x

  let apply (f : ('a -> 'b) option) (v : 'a option) =
    Option.bind (fun f' ->
      Option.bind (fun v' ->
        create (f' v')) v) f

  let lift2 f v1 v2 =
    apply (apply (create f) v1) v2

  let lift3 f v1 v2 v3 =
    apply (apply (apply (create f) v1) v2) v3

  let lift4 f v1 v2 v3 v4 =
    apply (apply (apply (apply (create f) v1) v2) v3) v4

  let lift5 f v1 v2 v3 v4 v5 =
    apply (apply (apply (apply (apply (create f) v1) v2) v3) v4) v5

  let ofChoice = function
    | Choice1Of2 x -> Some x
    | _ -> None

  let toChoice case2 = function
    | Some x -> Choice1Of2 x
    | None   -> Choice2Of2 case2

  let ofNullable nullable : 'a option =
    match box nullable with
    | null -> None // CLR null
    | :? Nullable<_> as n when not n.HasValue -> None // CLR struct
    | :? Nullable<_> as n when n.HasValue -> Some (n.Value) // CLR struct
    | x when x.Equals (DBNull.Value) -> None // useful when reading from the db into F#
    | x -> Some (unbox x) // anything else

  let toNullable = function
    | Some item -> new Nullable<_>(item)
    | None      -> new Nullable<_>()

  let orDefault x = function
    | None -> x
    | Some y -> y

  let inject f = function
    | Some x -> f x; Some x
    | None   -> None

  module Operators =

    let inline (>>=) m f =
      Option.bind f m

    let inline (=<<) f m =
      Option.bind f m

    let inline (>>*) m f =
      inject f m

    let inline (<*>) f m =
      apply f m

    let inline (<!>) f m =
      Option.map f m

    let inline ( *>) m1 m2 =
      lift2 (fun _ x -> x) m1 m2

    let inline ( <*) m1 m2 =
      lift2 (fun x _ -> x) m1 m2

type Base64String = string

module String =
  open System.IO
  open System.Security.Cryptography

  let equals (a : string) (b : string) =
    a.Equals(b, StringComparison.InvariantCulture)

  let contains (sub : string) (par : string) =
    par.Contains sub

  let trim (s : string) =
    s.Trim()

  let equalsConstantTime (str1 : string) (str2 : string) =
    let mutable xx = uint32 str1.Length ^^^ uint32 str2.Length
    let mutable i = 0
    while i < str1.Length && i < str2.Length do
      xx <- xx ||| uint32 (int str1.[i] ^^^ int str2.[i])
      i <- i + 1
    xx = 0u

  let toLowerInvariant (str : string) =
    str.ToLowerInvariant()

  let replace (find : string) (replacement : string) (str : string) =
    str.Replace(find, replacement)

  let sha1 (str : string) =
    use ms = new MemoryStream()
    use sw = new StreamWriter(ms)
    sw.Write str
    ms.Seek(0L, SeekOrigin.Begin) |> ignore
    use sha = SHA1.Create()
    sha.ComputeHash ms |> BitConverter.ToString |> fun s -> s.Replace("-", "")

module List =

  /// Split xs at n, into two lists, or where xs ends if xs.Length < n.
  let split n xs =
    let rec splitUtil n xs acc =
      match xs with
      | [] -> List.rev acc, []
      | _ when n = 0u -> List.rev acc, xs
      | x::xs' -> splitUtil (n - 1u) xs' (x::acc)
    splitUtil n xs []

  /// Chunk a list into pageSize large chunks
  let chunk pageSize = function
    | [] -> None
    | l -> let h, t = l |> split pageSize in Some(h, t)

  let first = function
    | [] -> None
    | x :: _ -> Some x

module Seq =

  let combinations size set =
    let rec combinations' acc size set =
      seq {
        match size, set with
        | n, x::xs ->
            if n > 0 then yield! combinations' (x::acc) (n - 1) xs
            if n >= 0 then yield! combinations' acc n xs
        | 0, [] -> yield acc
        | _, [] -> ()
      }
    combinations' [] size set

  let first (xs : _ seq) : _ option =
    if Seq.isEmpty xs then None else Seq.head xs |> Some

module Map =

  /// put a key to the map; if it's not there already, just add it
  /// otherwise, remove the existing key and place it there.
  let put k v m =
    match m |> Map.tryFind k with
    | Some _ -> m |> Map.remove k |> Map.add k v
    | None -> m |> Map.add k v

[<RequireQualifiedAccess>]
module Culture =
  open System.Globalization

  let invariant = CultureInfo.InvariantCulture

module UTF8 =
  open System.Text

  let private utf8 = Encoding.UTF8

  let toString (bs : byte []) =
    utf8.GetString bs

  let toStringAtOffset (b : byte []) (index : int) (count : int) =
    utf8.GetString(b, index, count)

  let bytes (s : string) =
    utf8.GetBytes s
  
  /// Encode the string as UTF8 encoded in Base64.
  let encodeBase64 : string -> Base64String =
    bytes >> Convert.ToBase64String

  let decodeBase64 : Base64String -> string =
    Convert.FromBase64String >> toString

module Comparisons =

  /// compare x to yobj mapped on selected value from function f
  let compareOn f x (yobj: obj) =
    match yobj with
    | :? 'T as y -> compare (f x) (f y)
    | _ -> invalidArg "yobj" "cannot compare values of different types"

  /// check equality on x and y mapped on selected value from function f
  let equalsOn f x (yobj:obj) =
    match yobj with
    | :? 'T as y -> (f x = f y)
    | _ -> false

  /// hash x on the selected value from f
  let hashOn f x =  hash (f x)

type Random with
  /// generate a new random ulong64 value
  member x.NextUInt64() =
    let buffer = Array.zeroCreate<byte> sizeof<UInt64>
    x.NextBytes buffer
    BitConverter.ToUInt64(buffer, 0)

module Bytes =
  open System.Linq
  open System.IO
  open System.Security.Cryptography

  let toHex (bs : byte[]) =
    BitConverter.ToString bs
    |> String.replace "-" ""
    |> String.toLowerInvariant

  let fromHex (digestString : string) =
    Enumerable.Range(0, digestString.Length)
              .Where(fun x -> x % 2 = 0)
              .Select(fun x -> Convert.ToByte(digestString.Substring(x, 2), 16))
              .ToArray()

  let hash (algo : HashAlgorithm) (bs : byte[]) =
    use ms = new MemoryStream()
    ms.Write(bs, 0, bs.Length)
    ms.Seek(0L, SeekOrigin.Begin) |> ignore
    use sha = algo
    sha.ComputeHash ms |> toHex

  let sha1 =
    hash (SHA1.Create())

  let equalsConstantTime (arr1 : 'a []) (arr2 : 'a []) =
    if arr1.Length <> arr2.Length then false else
    let mutable b = true
    for i in 0 .. arr1.Length - 1 do
      b <- b && (arr1.[i] = arr2.[i])
    b

module Regex =
  open System.Text.RegularExpressions

  let escape input =
    Regex.Escape input

  let split pattern input =
    Regex.Split(input, pattern)
    |> List.ofArray

  let replace pattern replacement input =
    Regex.Replace(input, pattern, (replacement : string))

  let ``match`` pattern input =
    match Regex.Matches(input, pattern) with
    | x when x.Count > 0 ->
      x
      |> Seq.cast<Match>
      |> Seq.head
      |> fun x -> x.Groups
      |> Some
    | _ -> None

module App =

  open System.IO
  open System.Reflection

  let Version =
    Assembly.GetCallingAssembly()
            .GetCustomAttribute<AssemblyInformationalVersionAttribute>()
            .InformationalVersion

  /// Get the assembly resource
  let resource name =
    let assembly = Assembly.GetExecutingAssembly ()
    use stream = assembly.GetManifestResourceStream name
    if stream = null then
      assembly.GetManifestResourceNames()
      |> Array.fold (fun s t -> sprintf "%s\n - %s" s t) ""
      |> sprintf "couldn't find resource named '%s', from: %s" name
      |> Choice2Of2
    else
      use reader = new StreamReader(stream)
      reader.ReadToEnd ()
      |> Choice1Of2

