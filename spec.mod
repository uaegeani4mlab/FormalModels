mod! SET(X :: TRIV) {
  [Elt < Set]
  -- empty set
  op empty : -> Set {constr}
  -- assicative and commutative set constructor with identity 'empty'
  op __ : Set Set -> Set {constr assoc comm id: empty} .
  -- __ is idempotent
  ceq (S:Set S) = S if not( S == empty ) .


  op _belongs_ : Elt Set -> Bool .
  eq (e:Elt belongs empty) = false .
  eq (e:Elt belongs (e2:Elt s:Set)) =  ((e = e2) or (e belongs s) ) .
}

mod* TOKEN {
    [Token]
  -- defines any uuid
}

mod! TOKEN-SET (X :: TOKEN) {
  -- set of tokens
  pr(SET(X{sort Elt -> Token})
     *{sort Set -> TS, op empty -> empTS})
}


mod* CLIENT {
    [ User < Client]
    -- denotes any user elements of the sort User
    -- and the owner or person behind the browser sending
    -- a front-channel  request Client
}

mod! ATTRIBUTES {
    [Attributes]
    pr(CLIENT)
    -- denotes the eIDAS set of attributes that "define" the given user
    op null : -> Attributes {constr} .
    op attr : User -> Attributes  {constr} .
    -- deconstructor
    op getUser : Attributes -> User .

    eq (null = null) = true .
    eq (null = attr:Attributes) = false .
}

mod* SENDER {
    [Sender]
    -- denotes any sender of an HTTP message
    -- constants
    op intruder : -> Sender . -- malicious user
    op iss : -> Sender . -- iss

    eq (intruder = iss) = false .
}



-- --------------------------------
-- OTS specification of protocol
-- --------------------------------

mod* SYSTEM {
    pr(TOKEN-SET)
    pr(ATTRIBUTES)
    pr(SENDER)
    *[Sys]*

  -- transitions
   op init : -> Sys {constr} .
   op startSession : Token -> Sys {constr} .
   op eidasAuth : Sys User  Token -> Sys {constr} .
   op issResponse :  Sys Attributes Sender Token -> Sys {constr} .
   -- authenticate the user using the token sent from the client
   op loginUser : Sys Token Client -> Sys {constr} .

  -- observers
   op issPending : Sys -> TS .
   op issReceivedAttributes : Sys Token -> Attributes .
   op spReceivedResponse : Sys Token -> Attributes .
   op loggedInUser : Sys Token -> User .
   -- the actual user that get authenticated through eIDAS
   op authNUser : Sys Token -> User .

  -- effective conditions
   op c-startSession :  Sys Token -> Bool .
   op c-eidasAuth : Sys Token -> Bool .
   op c-issResponse : Sys Token -> Bool .
   op c-loginUser : Sys Token  -> Bool .

  -- axioms

  -- loginUser  *the user logs in at the SP*
   eq c-loginUser(s:Sys,t:Token) = not (spReceivedResponse(s,t) = null) .
   eq issPending(loginUser(s:Sys,t:Token,c:Client)) = issPending(s) .
   eq issReceivedAttributes(loginUser(s:Sys,t:Token,c:Client),t2:Token) = issReceivedAttributes(s,t2) .
   eq spReceivedResponse(loginUser(s:Sys,t:Token,c:Client),t2:Token) = spReceivedResponse(s,t2)  .
   eq authNUser(loginUser(s:Sys,t:Token,c:Client),t2:Token) = authNUser(s,t2) .
   ceq loggedInUser(loginUser(s:Sys,t:Token,c:Client),t2:Token) = getUser(spReceivedResponse(s,t))
                                                                  if (t = t2) and  c = getUser(spReceivedResponse(s,t)) and c-loginUser(s,t) .
  ceq loggedInUser(loginUser(s:Sys,t:Token,c:Client),t2:Token) =  loggedInUser(s,t2)
                                                                  if not c-loginUser(s,t) .

  -- issResponse
   eq c-issResponse(s:Sys,t:Token) = (t belongs issPending(s)) .
   eq issPending(issResponse(s:Sys,a:Attributes,snd:Sender,t:Token)) = issPending(s) .
   eq issReceivedAttributes(issResponse(s:Sys,a:Attributes,snd:Sender,t:Token),t2:Token) = issReceivedAttributes(s,t2) .
   eq authNUser(issResponse(s:Sys,a:Attributes,snd:Sender,t:Token),t2:Token) = authNUser(s,t2) .
   ceq spReceivedResponse(issResponse(s:Sys,a:Attributes,snd:Sender,t:Token),t2:Token) =
                                            attr(authNUser(s,t2)) if (snd = iss)  and c-issResponse(s,t) and t = t2 .
   ceq spReceivedResponse(issResponse(s:Sys,a:Attributes,snd:Sender,t:Token),t2:Token) =
                                           spReceivedResponse(s,t2) if not c-issResponse(s,t) .
   eq loggedInUser(issResponse(s:Sys,a:Attributes,snd:Sender,t:Token),t2:Token) = loggedInUser(s,t2) .

  -- eidasAuth
  eq c-eidasAuth(s:Sys,t:Token) = t belongs  issPending(s) .
  eq issPending(eidasAuth(s:Sys,u:User,t:Token)) = issPending(s) .
  ceq issReceivedAttributes(eidasAuth(s:Sys,u:User,t:Token),t2:Token) =  attr(u)
                                                                         if c-eidasAuth(s,t) and t = t2 .
  ceq issReceivedAttributes(eidasAuth(s:Sys,u:User,t:Token),t2:Token) =  issReceivedAttributes(s,t2)
                                                                         if not( c-eidasAuth(s,t) and t = t2) .
  eq spReceivedResponse(eidasAuth(s:Sys,u:User,t:Token),t2:Token) = spReceivedResponse(s,t2)  .
  ceq authNUser(eidasAuth(s:Sys,u:User,t:Token),t2:Token) = u
                                                   if c-eidasAuth(s,t) .
  ceq authNUser(eidasAuth(s:Sys,u:User,t:Token),t2:Token) = authNUser(s,t)
                                                   if not c-eidasAuth(s,t) .
  eq loggedInUser(loginUser(s:Sys,t:Token,c:Client),t2:Token) = loggedInUser(s,t2) .

  -- startSession
  eq c-startSession(s:Sys,t:Token) = not (t belongs  issPending(s) ) .
  eq issPending(eidasAuth(s:Sys,u:User,t:Token)) = issPending(s) t .
  eq issReceivedAttributes(eidasAuth(s:Sys,u:User,t:Token),t2:Token) =  issReceivedAttributes(s,t2) .
  eq spReceivedResponse(eidasAuth(s:Sys,u:User,t:Token),t2:Token) = spReceivedResponse(s,t2)  .
  eq authNUser(eidasAuth(s:Sys,u:User,t:Token), t2:Token) = authNUser(s,t2) .
  eq loggedInUser(loginUser(s:Sys,t:Token,c:Client),t2:Token) = loggedInUser(s,t2) .


}
