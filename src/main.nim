# import nimprof
import httpclient, streams, re, system, asyncfutures
import strformat
import
  json, options, hashes, uri, strutils, tables, os, uri, strutils, md5,
  httpcore, parsexml, streams, asyncdispatch

import std/os
import std/httpcore
import std/json
import std/strutils
import std/uri
import std/algorithm
import std/sequtils
import std/tables
import std/times

when defined(sigv4UseNimCrypto):
  import nimcrypto/sha2 as sha
  import nimcrypto/hash as md
  import nimcrypto/hmac as hmac

  type
    MDigest256 = md.MDigest[256]
    MDigest512 = md.MDigest[512]

    SHA256Digest = sha.sha256
    SHA512Digest = sha.sha512

  proc computeSHA256(s: string): MDigest256 = md.digest(SHA256Digest, s)
  proc computeSHA512(s: string): MDigest512 = md.digest(SHA512Digest, s)

  proc newHmac(H: typedesc; key: string; data: string): auto =
    result = hmac.hmac(H, key, data)

  proc add(key: var MDigest256; data: string) =
    key = hmac.hmac(SHA256Digest, key.data, data)

  proc add(key: var MDigest512; data: string) =
    key = hmac.hmac(SHA512Digest, key.data, data)

else:
  import nimSHA2 as sha

  type
    MDigest256 = SHA256Digest
    MDigest512 = SHA512Digest

  # algo from https://github.com/OpenSystemsLab/hmac.nim/blob/master/hmac.nim
  # (rewritten to taste)
  proc hmac[T](key: string; data: string): T =
    const
      oxor = 0x5c
      ixor = 0x36

    when T is MDigest256:
      let hash = computeSHA256
      const ds = 32
      const bs = ds * 2

    when T is MDigest512:
      let hash = computeSHA512
      const ds = 64
      const bs = ds * 2

    var work = newSeq[uint8](bs)         # nicely typed bytes, yum!
    var inputs = newString(bs)           # inputs = block size
    var output = newString(bs + ds)      # output = block size + digest size

    # if it's larger than the block size, hash the key to shrink it
    let key = if len(key) > bs: $hash(key) else: key

    # copy the key over the work
    copyMem addr work[0], unsafeAddr key[0], len(key)

    # take the key and xor it against output, input constants
    for i, w in work.pairs:
      output[i] = char(w xor oxor)
      inputs[i] = char(w xor ixor)

    # add a hash of input + data to the end of the output
    let tail = hash(inputs & data)
    copyMem addr output[bs], unsafeAddr tail[0], len(tail)

    # the final result is a hash of the entire output
    result = hash(output)

  func newHmac(H: typedesc; key: string; data: string): auto =
    when H is SHA256Digest: result = hmac[MDigest256](key, data)
    when H is SHA512Digest: result = hmac[MDigest512](key, data)

  func add[H](key: var H; data: string) =
    key = hmac[H]($key, data)

const
  dateISO8601 = initTimeFormat "yyyyMMdd"
  basicISO8601 = initTimeFormat "yyyyMMdd\'T\'HHmmss\'Z\'"

type
  DateFormat = enum JustDate, DateAndTime
  PathNormal* = enum
    Default ## normalize paths to dereference `.` and `..` and de-dupe `/`
    S3 ## do not normalize paths, and perform one less pass of escaping
  SigningAlgo* = enum
    SHA256 = "AWS4-HMAC-SHA256"
    SHA512 = "AWS4-HMAC-SHA512"
    UnsignedPayload = "UNSIGNED-PAYLOAD"
  DigestTypes = MDigest256 or MDigest512
  EncodedHeaders* = tuple[signed: string; canonical: string]
  KeyValue = tuple[key: string; val: string]

proc encodedSegment(segment: string; passes: int): string =
  ## encode a segment 1+ times
  result = segment.encodeUrl(usePlus = false)
  if passes > 1:
    result = result.encodedSegment(passes - 1)

proc safeSplitPath(path: string): tuple[head, tail: string] =
  ## a split path that won't change with nim versions
  var sepPos = -1
  for i in countdown(len(path)-1, 0):
    if path[i] in {DirSep, AltSep}:
      sepPos = i
      break
  if sepPos >= 0:
    result.head = substr(path, 0, sepPos-1)
    result.tail = substr(path, sepPos+1)
  else:
    result.head = ""
    result.tail = path

proc encodedComponents(path: string; passes: int): string =
  ## encode an entire path with a number of passes
  if '/' notin path:
    return path.encodedSegment(passes)
  let
    splat = path.safeSplitPath
    tail = splat.tail.encodedSegment(passes)
  result = splat.head.encodedComponents(passes) & "/" & tail

proc encodedPath(path: string; style: PathNormal): string =
  ## normalize and encode a URI's path
  case style
  of S3:
    result = path
    result = result.encodedComponents(passes=1)
  of Default:
    result = path.normalizedPath
    when DirSep != '/':
      result = result.replace(DirSep, '/')
    if path.endsWith("/") and not result.endsWith("/"):
      result = result & "/"
    result = result.encodedComponents(passes=2)
  if not result.startsWith("/"):
    result = "/" & result

proc encodedQuery(input: openArray[KeyValue]): string =
  ## encoded a series of key/value pairs as a query string
  let
    query = input.sortedByIt (it.key, it.val)
  for q in query.items:
    if result.len > 0:
      result.add "&"
    result.add encodeUrl(q.key, usePlus = false)
    result.add "="
    result.add encodeUrl(q.val, usePlus = false)

proc toQueryValue(node: JsonNode): string =
  ## render a json node as a query string value
  assert node != nil
  if node == nil:
    raise newException(ValueError, "pass me a JsonNode")
  result = case node.kind
  of JString:
    node.getStr
  of JInt, JFloat, JBool:
    $node
  of JNull:
    ""
  else:
    raise newException(ValueError, $node.kind & " unsupported")

proc encodedQuery(node: JsonNode): string =
  ## convert a JsonNode into an encoded query string
  var query: seq[KeyValue]
  assert node != nil and node.kind == JObject
  if node == nil or node.kind != JObject:
    raise newException(ValueError, "pass me a JObject")
  for q in node.pairs:
    query.add (key: q.key, val: q.val.toQueryValue)
  result = encodedQuery(query)

proc normalizeUrl*(url: Uri; query: JsonNode; normalize: PathNormal = Default): Uri =
  ## reorder and encode path and query components of a url
  result = url
  result.path = encodedPath(result.path, normalize)
  result.query = encodedQuery query
  result.anchor = ""

proc normalizeUrl*(url: string; query: JsonNode; normalize: PathNormal = Default): Uri =
  ## reorder and encode path and query components of a url
  normalizeUrl(parseUri url, query, normalize = normalize)

proc trimAll(s: string): string =
  ## remove surrounding whitespace and de-dupe internal spaces
  result = s.strip(leading=true, trailing=true)
  while "  " in result:
    result = result.replace("  ", " ")

# a hack to work around nim 0.20 -> 1.0 interface change
template isEmptyAnyVersion(h: HttpHeaders): bool =
  when compiles(h.isEmpty):
    h.isEmpty
  else:
    h == nil

proc encodedHeaders(headers: HttpHeaders): EncodedHeaders =
  ## convert http headers into encoded header string
  var
    signed, canonical: string
    heads: seq[KeyValue]
  if headers.isEmptyAnyVersion:
    return (signed: "", canonical: "")
  # i know it's deprecated, but there's no reasonable replacement (yet)
  # https://github.com/nim-lang/Nim/issues/12211
  for h in headers.table.pairs:
    heads.add (key: h[0].strip.toLowerAscii,
               val: h[1].map(trimAll).join(","))
  heads = heads.sortedByIt (it.key)
  for h in heads:
    if signed.len > 0:
      signed &= ";"
    signed &= h.key
    canonical &= h.key & ":" & h.val & "\n"
  result = (signed: signed, canonical: canonical)

proc signedHeaders*(headers: HttpHeaders): string =
  ## calculate the list of signed headers
  var encoded = headers.encodedHeaders
  result = encoded.signed

when defined(sigv4UseNimCrypto):
  when defined(nimcryptoLowercase):
    proc toLowerHex(digest: DigestTypes): string =
      result = $digest
  else:
    proc toLowerHex(digest: DigestTypes): string =
      {.hint: "sigv4: set -d:nimcryptoLowercase".}
      # ...in order to optimize out the following call...
      result = toLowerAscii($digest)
else:
  proc toLowerHex(digest: DigestTypes): string =
    result = toLowerAscii(digest.toHex)

proc hash*(payload: string; digest: SigningAlgo): string =
  ## hash an arbitrary string using the given algorithm
  case digest
  of SHA256: result = computeSHA256(payload).toLowerHex
  of SHA512: result = computeSHA512(payload).toLowerHex
  of UnsignedPayload: result = $UnsignedPayload

proc canonicalRequest*(meth: HttpMethod; url: Uri; headers: HttpHeaders;
                       payload: string; digest: SigningAlgo = SHA256): string =
  ## produce the canonical request for signing purposes
  let
    httpmethod = $meth
    heads = headers.encodedHeaders()
  result = httpmethod.toUpperAscii & "\n"
  result.add url.path & "\n"
  result.add url.query & "\n"
  result.add heads.canonical & "\n"
  result.add heads.signed & "\n"
  result.add hash(payload, digest)

proc canonicalRequest*(meth: HttpMethod;
                      url: string;
                      query: JsonNode;
                      headers: HttpHeaders;
                      payload: string;
                      normalize: PathNormal = Default;
                      digest: SigningAlgo = SHA256): string =
  ## produce the canonical request for signing purposes
  var
    uri = parseUri url
  uri.path = encodedPath(uri.path, normalize)
  uri.query = encodedQuery query
  result = canonicalRequest(meth, uri, headers, payload, digest)

template assertDateLooksValid(d: string; format: DateFormat) =
  when not defined(release):
    case format
    of JustDate:
      if d.len > "YYYYMMDD".len:
        assert d["YYYYMMDD".len] == 'T'
      else:
        assert d.len == "YYYYMMDD".len
    of DateAndTime:
      if d.len > "YYYYMMDDTHHMMSS".len:
        assert d["YYYYMMDDTHHMMSS".len] == 'Z'
      else:
        assert d.len == "YYYYMMDDTHHMMSSZ".len

proc makeDateTime*(date: string = ""): string =
  ## produce a date+time string as found in stringToSign, eg. YYYYMMDDTHHMMSSZ
  if date == "":
    result = getTime().utc.format(basicISO8601)
  else:
    assertDateLooksValid(date, DateAndTime)
    result = date[date.low .. ("YYYYMMDDTHHMMSSZ".len-1)]

proc makeDate*(date: string = ""): string =
  ## produce a date string as required for credentialScope, eg. YYYYMMDD
  if date == "":
    result = getTime().utc.format(dateISO8601)
  else:
    assertDateLooksValid(date, JustDate)
    result = date[date.low .. ("YYYYMMDD".len-1)]

proc credentialScope*(region: string; service: string; date= ""): string =
  ## combine region, service, and date into a scope
  let d = date.makeDate
  result = d / region.toLowerAscii / service.toLowerAscii / "aws4_request"
  when DirSep != '/':
    result = result.replace(DirSep, '/')

proc stringToSign*(hash: string; scope: string; date= ""; digest: SigningAlgo = SHA256): string =
  ## combine signing algo, payload hash, credential scope, and date
  result = $digest & "\n"
  result.add date.makeDateTime & "\n"
  result.add scope & "\n"
  result.add hash

proc deriveKey(H: typedesc; secret: string; date: string;
               region: string; service: string): auto =
  ## compute the signing key for a subsequent signature
  result = newHmac(H, "AWS4" & secret, date.makeDate)
  result.add region.toLowerAscii
  result.add service.toLowerAscii
  result.add "aws4_request"

proc calculateSignature*(secret: string; date: string; region: string;
                         service: string; tosign: string;
                         digest: SigningAlgo = SHA256): string =
  ## compute a signature using secret, string-to-sign, and other details
  case digest
  of SHA256:
    var key = deriveKey(SHA256Digest, secret, date, region, service)
    key.add tosign
    result = key.toLowerHex
  of SHA512:
    var key = deriveKey(SHA512Digest, secret, date, region, service)
    key.add tosign
    result = key.toLowerHex
  of UnsignedPayload:
    discard

type
  XAmz = enum
    SecurityToken = "X-Amz-Security-Token", ContentSha256 = "X-Amz-Content-Sha256"

proc rawListObjectsV2(
  client: HttpClient,
  bucket: string,
  prefix = "",
  secret = "",
  access = "",
  region = "",
  session_token = "",
  delimiter = "",
  start_after = "",
  continuation_token = ""
): Response =
  let session = getEnv("AWS_SESSION_TOKEN", session_token)
  let access = os.getEnv("AWS_ACCESS_KEY_ID", access)
  let secret = os.getEnv("AWS_SECRET_ACCESS_KEY", secret)
  let region = os.getEnv("AWS_REGION", region)
  assert secret != "", "need $AWS_SECRET_ACCESS_KEY in environment"
  assert access != "", "need $AWS_ACCESS_KEY_ID in environment"
  assert region != "", "need $AWS_REGION in environment"

  let normal = PathNormal.S3
  let host = bucket & ".s3." & region & ".amazonaws.com"
  var query = %*
    {
      "list-type": "2",
      "delimiter": delimiter,
      "prefix": prefix,
      "start-after": start_after
    }
  if continuation_token != "":
    query.add("continuation-token", %* continuation_token)
  let url = $normalizeUrl("https://" & host, query, normal)

  let algo = SHA256
  let date = makeDateTime()

  var headers = newHttpHeaders({
    "content-type": "application/x-amz-json-1.0",
    $SecurityToken: session,
    "X-Amz-Date": date,
    "Host": host,
    $ContentSha256: hash("", SHA256)
  })

  let
    scope = credentialScope(region = region, service = "S3", date = date)
    request = canonicalRequest(
      HttpMethod.HttpGet,
      "/",
      query,
      headers,
      "",
      normalize = normal,
      digest = algo
    )
    sts = stringToSign(request.hash(algo), scope, date = date, digest = algo)
    signature = calculateSignature(secret = secret, date = date, region = region,
                                  service = "S3", sts, digest = algo)
  var auth = $algo & " "
  auth &= "Credential=" & access / scope & ", "
  auth &= "SignedHeaders=" & headers.signedHeaders & ", "
  auth &= "Signature=" & signature
  headers["Authorization"] = auth

  return client.request(
    url, headers=headers
  )

type
  Owner = object
    displayName: string
    id: string

  Contents = object
    eTag: string
    key: string
    lastModified: string
    owner: Owner
    size: int64
    storageClass: string

  CommonPrefixes = object
    prefix: string

  ListBucketResult = object
   isTruncated: bool
   contents: seq[Contents]
   name: string
   prefix: string
   delimiter: string
   maxKeys: int64
   commonPrefixes: seq[CommonPrefixes]
   encodingType: string
   keyCount: int64
   continuationToken: string
   nextContinuationToken: string
   startAfter: string

proc `$`(o: Owner): string =
  return fmt"""{{"displayName": "{o.displayName}", "id": "{o.id}"}}"""

proc `$`(c: Contents): string =
  return fmt"""{{"key": "{c.key}", "size": {c.size}, "lastModified": "{c.lastModified}", "eTag": {c.eTag}, "owner": {c.owner}, "storageClass": "{c.storageClass}"}}"""

proc rawParseStringTag(x: var XmlParser, tag: string): string =
  assert x.kind == xmlElementStart
  assert x.elementName == tag
  x.next()
  while x.kind == xmlCharData:
    result.add(x.charData)
    x.next()
  assert x.kind == xmlElementEnd and x.elementName == tag
  x.next()

proc rawParseCommonPrefixes(x: var XmlParser): CommonPrefixes =
  assert x.kind == xmlElementStart
  assert x.elementName == "CommonPrefixes"
  x.next()
  let prefix = rawParseStringTag(x, "Prefix")
  assert x.kind == xmlElementEnd and x.elementName == "CommonPrefixes"
  x.next()
  return CommonPrefixes(prefix: prefix)

proc rawParseOwner(x: var XmlParser): Owner =
  assert x.kind == xmlElementStart
  assert x.elementName == "Owner"
  x.next()
  while x.kind == xmlElementStart:
    case x.elementName
    of "DisplayName":
      result.displayName = rawParseStringTag(x, "DisplayName")
    of "ID":
      result.id = rawParseStringTag(x, "ID")
    else:
      raise newException(KeyError, "Owner must have only DisplayName and ID")
  assert x.kind == xmlElementEnd and x.elementName == "Owner"
  x.next()

proc rawParseContents(x: var XmlParser): Contents =
  assert x.kind == xmlElementStart
  assert x.elementName == "Contents"
  x.next()
  while x.kind == xmlElementStart:
    case x.elementName
    of "ETag":
      result.eTag = rawParseStringTag(x, "ETag")
    of "Key":
      result.key = rawParseStringTag(x, "Key")
    of "LastModified":
      result.lastModified = rawParseStringTag(x, "LastModified")
    of "Owner":
      result.owner = rawParseOwner(x)
    of "Size":
      result.size = parseInt(rawParseStringTag(x, "Size"))
    of "StorageClass":
      result.storageClass = rawParseStringTag(x, "StorageClass")
    else:
      raise newException(KeyError, "Invalid tag inside Contents")
  assert x.kind == xmlElementEnd and x.elementName == "Contents"
  x.next()

proc rawParseListBucketResult(x: var XmlParser): ListBucketResult =
  assert x.kind == xmlElementOpen or x.kind == xmlElementStart
  if x.elementName != "ListBucketResult":
    echo "parsing ListBucketResult failed, first element=", x.elementName
    assert(false)
  while x.kind != xmlElementStart:
    x.next()
  while x.kind == xmlElementStart:
    case x.elementName
    of "IsTruncated":
      result.isTruncated = parseBool(rawParseStringTag(x, "IsTruncated"))
    of "Contents":
      result.contents.add(rawParseContents(x))
    of "Name":
      result.name = rawParseStringTag(x, "Name")
    of "Prefix":
      result.prefix = rawParseStringTag(x, "Prefix")
    of "Delimiter":
      result.delimiter = rawParseStringTag(x, "Delimiter")
    of "MaxKeys":
      result.maxKeys = parseInt(rawParseStringTag(x, "MaxKeys"))
    of "CommonPrefixes":
      result.commonPrefixes.add(rawParseCommonPrefixes(x))
    of "EncodingType":
      result.encodingType = rawParseStringTag(x, "EncodingType")
    of "KeyCount":
      result.keyCount = parseInt(rawParseStringTag(x, "KeyCount"))
    of "ContinuationToken":
      result.continuationToken = rawParseStringTag(x, "ContinuationToken")
    of "NextContinuationToken":
      result.nextContinuationToken = rawParseStringTag(x, "NextContinuationToken")
    of "StartAfter":
      result.startAfter = rawParseStringTag(x, "StartAfter")
    else:
      raise newException(KeyError, "Invalid tag in ListBucketResult")
  assert x.kind == xmlElementEnd and x.elementName == "ListBucketResult"
  x.next()

proc parseListBucketResult(body: string, filename = "yesfile"): ListBucketResult =
  var x: XmlParser
  x.open(newStringStream(body), filename)
  x.next()
  return x.rawParseListBucketResult()

proc listObjectsV2(
  client: HttpClient,
  bucket: string,
  prefix = "",
  secret = "",
  access = "",
  region = "",
  session_token = "",
  delimiter = "",
  start_after = "",
  continuation_token = "",
  filename = ""
): ListBucketResult =
  return client.rawListObjectsV2(
    bucket = bucket,
    prefix = prefix,
    secret = secret,
    access = access,
    region = region,
    session_token = session_token,
    delimiter = delimiter,
    start_after = start_after,
    continuation_token = continuation_token
  ).body.parseListBucketResult(filename = filename)

proc recursiveListObjects(
  client: HttpClient,
  bucket: string,
  prefix = "",
  secret = "",
  access = "",
  region = "",
  session_token = "",
  delimiter = "",
  start_after = ""
): seq[Contents] =
  var results = client.listObjectsV2(
    bucket = bucket,
    prefix = prefix,
    secret = secret,
    access = access,
    region = region,
    session_token = session_token,
    delimiter = delimiter,
    start_after = start_after
  )
  var token = results.nextContinuationToken
  # results.contents.map(`$`).apply(proc(item: string) = echo item)
  result.add(results.contents)
  while token != "":
    results = client.listObjectsV2(
      bucket = bucket,
      prefix = prefix,
      secret = secret,
      access = access,
      region = region,
      session_token = session_token,
      delimiter = delimiter,
      continuation_token = token
    )
    # results.contents.map(`$`).apply(proc(item: string) = echo item)
    result.add(results.contents)
    token = results.nextContinuationToken

const supported_chars = " !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~"
const max_key_length = 1024

proc getLastKeyWithPrefix(prefix: string): string =
  if prefix.len() < max_key_length:
    return prefix & supported_chars[^1].repeat(max_key_length - prefix.len())

proc getBisectKey(startAfter: string, stopAt: string, bisectPrefix: bool): string =
  let (i, lastCommonSlash) = block:
    var
      i = 0
      lastCommonSlash = -1
    let max_len = min(startAfter.len(), stopAt.len())
    while i < max_len and startAfter[i] == stopAt[i]:
      if startAfter[i] == '/':
        lastCommonSlash = i
      i += 1
    (i, lastCommonSlash)
  
  let charIndex1 = block:
    if i == startAfter.len():
      0
    else:
      supported_chars.find(startAfter[i])
  let charIndex2 = supported_chars.find(stopAt[i])

  # echo "char indices: ", charIndex1, " ", charIndex2

  if bisectPrefix and i < startAfter.len():
    let key = startAfter[0..startAfter.find('/', lastCommonSlash + 1)]
    if key.len() > 0:
      # echo "here0"
      return getLastKeyWithPrefix(key)

  if charIndex1 + 1 == charIndex2:
    # echo "here1"
    return startAfter[0..i] & supported_chars[int(
      (
        supported_chars.len() -
        1 +
        supported_chars.find(startAfter[i + 1])
      ) / 2
    )]
  else:
    # echo "here2"
    return (
      startAfter[0..i - 1] & supported_chars[int(
        (
          charIndex1 + charIndex2
        ) / 2
      )]
    )
  
proc readContentsFile(filepath: string): (seq[string], seq[ref Contents]) =
  var strm = newFileStream(filepath, fmRead)
  var lines: seq[string]
  var contents: seq[ref Contents]
  var line = ""

  if not isNil(strm):
    while strm.readLine(line):
      var matches: array[7, string]
      if re.match(
        line,
        re"""^\{"key": "(.*)", "size": (\d+), "lastModified": "(.*)", "eTag": (.*), "owner": \{"displayName": "(.*)", "id": "(.*)"}, "storageClass": "(.*)"}$""",
        matches
      ):
        system.add(lines, matches[0])
        contents.add((ref Contents)(
          key: matches[0]
        ))
      else:
        echo line
        assert(false)

    strm.close()
  return (lines, contents)

proc recursiveListObjects(
  client: (seq[string], seq[ref Contents]),
  bucket: string,
  prefix = "",
  secret = "",
  access = "",
  region = "",
  session_token = "",
  delimiter = "",
  start_after = "",
  max_keys = 1000
): Future[seq[ref Contents]] {.async.} =
  let i = upperBound(client[0], startAfter, system.cmp[string])
  return client[1][i..min(i+max_keys-1, client[1].high)]

type
  ListNode = tuple[objs: ref ListNodeObj, total:int]
  ListSubNode = object
    shallow: seq[ref Contents]
    deep: ListNode
  ListNodeObj = tuple[left: ListSubNode, right: ListSubNode]

proc rawFlatten(res: var seq[ref Contents], listNode: ListNode, depth = 0) =
  assert depth < 100
  # echo depth
  res.add(listNode.objs[0].shallow)
  if listNode.objs[0].deep.objs != nil:
    res.rawFlatten(listNode.objs[0].deep, depth+1)
    
  res.add(listNode.objs[1].shallow)
  if listNode.objs[1].deep.objs != nil:
    res.rawFlatten(listNode.objs[1].deep, depth+1)

proc flatten(listNode: ListNode): seq[ref Contents] = result.rawFlatten(listNode)
  

proc recursiveList[T](
  client: T,
  bucket: string,
  secret = "",
  access = "",
  region = "",
  session_token = "",
  start_after = "",
  stop_at = getLastKeyWithPrefix(""),
  max_keys = 1000,
  useBisectPrefix = false;
  depth = 0
): Future[ListNode] {.async.} =
  if depth >= 100:
    assert(false)
  # echo "\ndepth=", depth
  # echo "start_after='", start_after, "'"
  # echo "stop_at='", stop_at, "'"
  let middleKey = getBisectKey(start_after, stop_at, useBisectPrefix)
  assert start_after <= middleKey
  assert middleKey <= stop_at
  # echo "middleKey = ", middleKey
  let calls = block:
    [start_after, middleKey]
    .map(proc(key: string): Future[seq[ref Contents]] = recursiveListObjects(
      client = client,
      bucket = bucket,
      secret = secret,
      access = access,
      region = region,
      session_token = session_token,
      start_after = key,
      max_keys = max_keys
    ))
  
  let calls2 = [await calls[0], await calls[1]]
  # echo "lens: ", calls2[0].len(), " ", calls2[1].len()

  let calls3 = [
    calls2[0].filter(
      proc(c: ref Contents): bool = c.key <= middleKey
    ),
    calls2[1].filter(
      proc(c: ref Contents): bool = c.key <= stop_at
    )
  ]

  let usePrefixBisect = [
    calls3[1].len() == 0,
    false
  ]

  var recursive_calls: seq[Future[ListNode]]
  var called = [false, false]

  for i, key_stop_at in [middleKey, stop_at]:
    if calls2[i].len() >= max_keys and calls2[i][^1].key < key_stop_at:
      called[i] = true
      # echo "first ret[", i, "]: ", calls2[i][0]
      # echo "last ret[", i, "]: ", calls2[i][^1]
      # echo "calling on[", i, "]: ", calls2[i][^1].key, ", ", key_stop_at
      recursive_calls.add(
        recursiveList(
          client = client,
          bucket = bucket,
          secret = secret,
          access = access,
          region = region,
          session_token = session_token,
          start_after = calls2[i][^1].key,
          stop_at = key_stop_at,
          max_keys = max_keys,
          useBisectPrefix = usePrefixBisect[i],
          depth = depth + 1
        )
      )
  
  var recursive_res: seq[ListNode]
  for call in recursive_calls:
    recursive_res.add(await call)

  result.total = calls3[0].len() + calls3[1].len()
  if called[0]:
    result.total += recursive_res[0].total
  if called[1]:
    result.total += recursive_res[int(called[0])].total

  if result.total == 0:
    return

  new(result.objs)

  result.objs[0].shallow = calls3[0]

  if called[0]:
    result.objs[0].deep = recursive_res[0]

  result.objs[1].shallow = calls3[1]

  if called[1]:
    result.objs[1].deep = recursive_res[int(called[0])]

  echo "depth=", depth, ", returned=", result.total

# proc recursiveList[T](
#   client: T,
#   bucket: string,
#   secret = "",
#   access = "",
#   region = "",
#   session_token = ""
# ): Future[seq[Contents]] {.async.} =
#   return await innerRecursiveList(
#     client = client,
#     bucket = bucket,
#     secret = secret,
#     access = access,
#     region = region,
#     session_token = session_token,
#     start_after = "",
#     stop_at = getLastKeyWithPrefix("")
#   )

let bucket = paramStr(1)
# let prefix = block:
#   if paramCount() > 1:
#     paramStr(2)
#   else:
#     ""

# var client = newHttpClient()
# let res = client.recursiveListObjects(bucket, prefix)

let (keys, contents) = expandTilde("~/src/nims3/example.full").readContentsFile()

let keys2 = (
  (keys, contents)
  .recursiveList(bucket)
  .waitFor()
  .flatten()
  .map(proc(item: ref Contents): string = item.key)
  # .apply(proc(item: string) = echo item)
)

echo "equating..."

# echo keys[1000], " ", keys2[999 .. 1000]
assert keys == keys2
