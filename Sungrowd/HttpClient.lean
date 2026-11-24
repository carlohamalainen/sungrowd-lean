/-! # An HTTP(S) client, for ntfy, Prometheus and Solcast

`Std` has an HTTP server but no client (and no TLS) yet, so this runs `curl`. The whole request
(URL, headers, body, query parameters) goes to curl on stdin as a config file (`--config -`),
never on its command line, where other users could read a secret like Solcast's API key with
`ps`. Everything that talks HTTP goes through `httpRequest`, so a native client can replace curl
here alone. -/

namespace Sungrowd

structure HttpResponse where
  status : Nat
  body   : String

/-- A double-quoted string in curl's config syntax. -/
def curlQuote (s : String) : String :=
  "\"" ++ s.foldl (init := "") (fun acc c => acc ++ match c with
    | '\\' => "\\\\"
    | '"'  => "\\\""
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c    => c.toString) ++ "\""

#guard curlQuote "a \"b\"\\\nc" == "\"a \\\"b\\\"\\\\\\nc\""

/-- curl's config for one request. With `query`, a GET whose parameters curl URL-encodes. -/
def curlConfig (method url : String) (headers : List (String × String))
    (query : List (String × String)) (body : Option String) (timeoutS : Nat) : String :=
  let line (k v : String) := s!"{k} = {curlQuote v}\n"
  "silent\nshow-error\n" ++
  line "max-time" (toString timeoutS) ++
  line "write-out" "\n%{http_code}" ++
  line "request" method ++
  String.join (headers.map fun (k, v) => line "header" s!"{k}: {v}") ++
  (if query.isEmpty then "" else "get\n") ++
  String.join (query.map fun (k, v) => line "data-urlencode" s!"{k}={v}") ++
  (body.map (line "data-binary" ·)).getD "" ++
  line "url" url

/-- One request. Errors are transport failures (curl's message, e.g. `curl: (7) Failed to
connect …`); any HTTP status is a response, for the caller to judge. -/
def httpRequest (method url : String) (headers : List (String × String) := [])
    (query : List (String × String) := []) (body : Option String := none) (timeoutS : Nat := 10) :
    IO (Except String HttpResponse) := do
  try
    let child ← IO.Process.spawn {
      cmd := "curl", args := #["--config", "-"]
      stdin := .piped, stdout := .piped, stderr := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.putStr (curlConfig method url headers query body timeoutS)
    stdin.flush
    -- `stdin` is closed after its last use, so curl sees the end of its config.
    let out ← child.stdout.readToEnd
    let err ← child.stderr.readToEnd
    if (← child.wait) != 0 then return .error err.trimAscii.toString
    -- The body, then the status on a line of its own (`write-out`).
    let lines := out.splitOn "\n"
    let some status := (lines.getLast?.getD "").toNat?
      | return .error s!"curl: no HTTP status in its output"
    return .ok ⟨status, "\n".intercalate lines.dropLast⟩
  catch e => return .error (toString e)

/-- Go's error `snippet`: the first 200 characters of a body. -/
def snippet (s : String) : String := String.ofList (s.toList.take 200)

end Sungrowd
