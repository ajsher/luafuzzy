--
-- Lua Fuzzy Example
--
-- This example use a fuzzy system the define the "right" amount to tip
-- a waiter, based on the quality of the sevice at a restaurant.
--   
--
-- Lucas Lorensi 05-2008
--

--
-- Load Fuzzy Lua Framework
--
require 'luafuzzy'

---------------------------------
-- Fuzzy System
---------------------------------

local fuzzy = luafuzzy()

---------------------------------
-- Fuzzy Inputs
---------------------------------

--
-- Service
--
local serv = fuzzy:addinp( 'service', 0, 10 )
serv:addlingvar( 'poor', gaussmf, { 1.5, 0. } )
serv:addlingvar( 'good', gaussmf, { 1.5, 5. } )
serv:addlingvar( 'excellent', gaussmf, { 1.5, 10. } )

--
-- Food
--
local food = fuzzy:addinp( 'food', 0, 10 )
food:addlingvar( 'rancid', trapmf, { 0, 0, 1, 3 } )
food:addlingvar( 'delicious', trapmf, { 7, 9, 10, 10 } )


---------------------------------
-- Fuzzy Outputs
---------------------------------


--
-- Tip
--
local tip = fuzzy:addout( 'tip', 0, 30 )
tip:addlingvar( 'cheap', trimf, { 0, 5, 10 } )
tip:addlingvar( 'average', trimf, { 10, 15, 20 } )
tip:addlingvar( 'generous', trimf, { 20, 25, 30 } )


---------------------------------
-- Rules
---------------------------------

--
-- Rule 1
--
local r1 = fuzzy:addrule( 1, 'ormethod' )
r1:addpremise( false, 'service', 'poor' )
r1:addpremise( false, 'food', 'rancid' )
r1:addimplic( false, 'tip', 'cheap' )

--
-- Rule 2
--
local r2 = fuzzy:addrule( 1, 'andmethod' )
r2:addpremise( false, 'service', 'good' )
r2:addimplic( false, 'tip', 'average' )

--
-- Rule 3
--
local r3 = fuzzy:addrule( 1, 'ormethod' )
r3:addpremise( false, 'service', 'excellent' )
r3:addpremise( false, 'food', 'delicious' )
r3:addimplic( false, 'tip', 'generous' )

---------------------------------
-- Evaluate...
---------------------------------
print( fuzzy:solve( 8.0, 6.5 ) )
