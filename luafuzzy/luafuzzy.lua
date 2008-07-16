-------------------------------------------------------------------------------
-- Lua Fuzzy system
--
--
-- ToDo: 
--  - Use the 'weight' field of rules
--  - Use the 'neg' field of rules
--
-- Licensed under the same terms as Lua itself.
--
-- @author Lucas Lorensi (lucas.lorensi@gmail.com)
--
-- @release $ v0.1 2008/05/21 $
-------------------------------------------------------------------------------


---------------------------------
-- Fuzzy Operations
---------------------------------


-------------------------------------------------------------------------------
-- Tmin
-------------------------------------------------------------------------------
function tmin(a1,a2)
  if a2 < a1 then
    return a2
  else
    return a1
  end
end

-------------------------------------------------------------------------------
-- Tmax
-------------------------------------------------------------------------------
function tmax(a1,a2)
  if a2 < a1 then
    return a1
  else
    return a2
  end
end

-------------------------------------------------------------------------------
-- Tsum
-------------------------------------------------------------------------------
function tsum(a1,a2)
  local y = a1 + a2
  if y > 1 then y = 1 end -- stop in one(limit)?
  return y 
end

-------------------------------------------------------------------------------
-- Tprod
-------------------------------------------------------------------------------
function prod(a1,a2)
  local y = a1*a2
  if y > 1 then y = 1 end -- stop in one(limit)?
  return y 
end


---------------------------------
-- Membership Functions
---------------------------------


-------------------------------------------------------------------------------
-- Gaussian membership function
-- @param x Input value
-- @param params Table of parameters: 
--   - params[1] = standard deviation 
--   - params[2] = mean
-- @return The value of the pertinence
-------------------------------------------------------------------------------
function gaussmf( x, params )
  return math.exp( -((x - params[2])^2)/(2*params[1]^2))
end

-------------------------------------------------------------------------------
-- Trapezoidal membership function
-- @param x Input value
-- @param params Table of parameters(see chart below)
-- @return The value of the pertinence
--
-- pertinency
--   ^
--   |
--   |  /2+++3\  
--   | /       \
--  -|1---------4-->x
-------------------------------------------------------------------------------
function trapmf( x, params)
  if x > params[1] and x < params[2] then
    return (x-params[1])/(params[2]-params[1])
  elseif x >= params[2] and x < params[3] then
    return 1
  elseif x >= params[3] and x < params[4] then
    return (params[4]-x)/(params[4]-params[3])
  else
    return 0
  end
end

-------------------------------------------------------------------------------
-- Triangular membership function
-- @param x Input value
-- @param params Table of parameters(see chart below)
-- @return The value of the pertinence
--
-- pertinency
--   ^
--   |
--   |  /2\  
--   | /   \
--  -|1-----3-->x
-------------------------------------------------------------------------------
function trimf( x, params )
  if x > params[1] and x < params[2] then
    return (x-params[1])/(params[2]-params[1])
  elseif x >= params[2] and x < params[3] then
    return  (params[3]-x)/(params[3]-params[2])
  else
    return 0
  end
end


---------------------------------
-- Deffuzification Functions
---------------------------------


-------------------------------------------------------------------------------
-- Centroid deffuzyfication method
-- @param fs A fuzzyset with pairs of x and y like: fs[1].x, fs[1].y
-- @returm Return the geometric center value
-------------------------------------------------------------------------------
function centroid( fs )
  if #fs <= 1 then
    error('invalid number of entries in the fuzzyset')
  end
  local accxy = 0
  local accy = 0
  for i,v in ipairs(fs) do    
    if v.y > 0 then
      accxy = accxy + v.x*v.y
      accy = accy + v.y
    end
  end
  if accy > 0 then  
    return accxy/accy
  else
    return (fs[1]-fs[#fs])/2
  end
end


---------------------------------
-- Fuzzy Inference System
---------------------------------


-------------------------------------------------------------------------------
-- Method to solve a fuzzy system
-- @param self The fuzzy system
-- @param ... A vararg list of input values
-- @return A vararg list of output values
-------------------------------------------------------------------------------
local function solvefuzzy( self, ... )
  local fuzzy = self
  local inpvals = {...}

  -- error check
  if #fuzzy.inps <= 0 then error('invalid number of inputs') end
  if #fuzzy.outs <= 0 then error('invalid number of outputs') end
  if #fuzzy.rules <= 0 then error('invalid number of rules') end

  -- solve each input
  for i,inp in ipairs(fuzzy.inps) do

    -- current input value
    local x = inpvals[i]
    
    -- error check
    if x > inp.mx or x < inp.mn then
      error('value ' .. x .. ' out of range for input \'' .. inp.name .. '\'')
    end

    -- save the current value of the function for each lingvar
    for _,lg in pairs(inp.lingvars) do
      lg.value = lg.mf( x, lg.params )
    end
  end

  -- for each rule...
  for ri,r in ipairs(fuzzy.rules) do
  
    --
    -- Errors Check
    --

    -- range errors check
    if #r.pres <= 0 then error('invalid number of premises') end
    if #r.imps <= 0 then error('invalid number of implications') end
    
    -- premises errors check
    for pi=1,#r.pres do
      if not fuzzy.inps[r.pres[pi].ifpart] then 
        error('invalid \'if part = '..r.pres[pi].ifpart..'\' for premise '..pi..' of rule ' .. ri) 
      end      
      if not fuzzy.inps[r.pres[pi].ifpart].lingvars[r.pres[pi].ispart] then
        error('invalid \'is part = '..r.pres[pi].ispart..'\' for premise '..pi..' of rule ' .. ri) 
      end
    end
    
    -- implications errors check
    for ii,imp in ipairs(r.imps) do
      if not fuzzy.outs[imp.thenpart] then 
        error('invalid \'then part = '..imp.thenpart..'\' for implication '..ii..' of rule ' .. ri) 
      end      
      if not fuzzy.outs[imp.thenpart].lingvars[imp.ispart] then 
        error('invalid \'is part = '..imp.ispart..'\' for implication '..ii..' of rule ' .. ri) 
      end      
    end
    
    -- connection function error check
    if not fuzzy[r.connmethod] then
      error('invalid \'connection method = '..r.connmethod..'\' for rule '..ri..'. (must be \'andmethod\' or \'ormethod\')') 
    end
    
    --
    -- Calculate the result value for a rule...
    --

    -- retrive the connection function
    local conn = fuzzy[r.connmethod]
    
    -- result value of premises
    r.value = fuzzy.inps[r.pres[1].ifpart].lingvars[r.pres[1].ispart].value

    -- for each premise...
    for pi=2,#r.pres do
      local v = fuzzy.inps[r.pres[pi].ifpart].lingvars[r.pres[pi].ispart].value
      r.value = conn(v, r.value)
    end
    
    --
    -- Calculate the resulting fuzzyset for each implication...
    --

    for _,imp in ipairs(r.imps) do

      -- retrive the out's table
      local out = fuzzy.outs[imp.thenpart]

      -- retrive the lingvar from the out table
      local lg = out.lingvars[imp.ispart]

      -- save the fuzzyset for each implication
      imp.fuzzyset = {}
      
      -- compute the step
      local step = (out.mx - out.mn)*fuzzy.step

      -- calculate the resulting fuzzyset
      for i=out.mn,out.mx,step do

        -- computes the mf value for i
        local lgval = lg.mf( i, lg.params )        

        -- compute the implication result
        local v = fuzzy.implicmethod( lgval , r.value )

        -- add the result to the fuzzy set
        table.insert( imp.fuzzyset, { x=i, y=v } )
      end
    end -- end implications
  end -- end rules

  --
  -- Computes output...
  --

  -- result table
  local outvals = {}

  -- solve each output
  for i,out in ipairs(fuzzy.outs) do

    -- clear previews fuzzyset
    out.fuzzyset = nil
    
    -- for each rule...
    for _,r in ipairs(fuzzy.rules) do

      --
      -- Aggregation
      --

      -- for each implication
      for _,imp in ipairs(r.imps) do

        if out.name == imp.thenpart then

          if not out.fuzzyset then
            out.fuzzyset = {}
            -- copy the first implication fuzzyset
            for k,v in ipairs(imp.fuzzyset) do
              out.fuzzyset[k] = { x=v.x, y=v.y }
            end
          else
            -- calculate the resulting fuzzyset with aggregation method
            for i,v in ipairs(out.fuzzyset) do
              -- computes the new value
              out.fuzzyset[i] = { x=v.x, y = fuzzy.aggregmethod( v.y, imp.fuzzyset[i].y ) }
            end
          end
        end
      end
    end

    --
    -- Defuzzification...
    --

    -- call deffuzyfication method
    out.value = fuzzy.defuzzmethod( out.fuzzyset )
    -- add output value to result table
    table.insert( outvals, out.value )    
  end

  return unpack( outvals )
end


---------------------------------
-- Fuzzy System
---------------------------------


-------------------------------------------------------------------------------
-- Method to add a new linguistic variable to a fuzzy input or output
-- @param self The variable's table
-- @param name Name of the variable
-- @param mf The membership function
-- @param params Table of parameters of the membership function
-- @return The lingvar's table
-------------------------------------------------------------------------------
local function addlingvar( self, name, mf, params )
  local var = self
  local lg = {}
  lg.name = name
  lg.mf = mf
  lg.params = params
  var.lingvars[lg.name] = lg
  return lg  
end

-------------------------------------------------------------------------------
-- Method to add a new input variable to a fuzzy system
-- @param self The fuzzy system table
-- @param name Name of the variable
-- @param mn Lower limit of values
-- @param mx Upper limit of values
-- @return The variable's table
-------------------------------------------------------------------------------
local function addinp( self, name, mn, mx )
  local fis = self
  local inp = {}
  inp.name = name
  inp.mn = mn
  inp.mx = mx
  inp.lingvars = {}     
  inp.addlingvar = addlingvar  
  table.insert( fis.inps, inp )
  fis.inps[inp.name] = inp
  return inp
end

-------------------------------------------------------------------------------
-- Method to add a new output variable to a fuzzy system
-- @param self The fuzzy system table
-- @param name Name of the variable
-- @param mn Lower limit of values
-- @param mx Upper limit of values
-- @return The variable's table
-------------------------------------------------------------------------------
local function addout( self, name, mn, mx )
  local fis = self
  local out = {}
  out.name = name
  out.mn = mn
  out.mx = mx
  out.lingvars = {}     
  out.addlingvar = addlingvar  
  table.insert( fis.outs, out )
  fis.outs[out.name] = out
  return out
end

-------------------------------------------------------------------------------
-- Method to add a new premise to a rule
-- @param self The rule's table
-- @param neg Flag to informe if the implication output should be negated
-- @param ifpart Name of the input variable
-- @param ispart Name of the linguistic variable of the input
-- @return The premises table
-------------------------------------------------------------------------------
local function addpremise( self, neg, ifpart, ispart )
  local rule = self
  local prem = {}
  prem.neg = neg
  prem.ifpart = ifpart
  prem.ispart = ispart
  table.insert( rule.pres, prem )
  return prem
end

-------------------------------------------------------------------------------
-- Method to add a new implication to a rule
-- @param self The rule's table
-- @param neg Flag to informe if the implication output should be negated
-- @param thenpart Name of the output variable
-- @param ispart Name of the linguistic variable of the ouput
-- @return The implication's table
-------------------------------------------------------------------------------
local function addimplic( self, neg, thenpart, ispart )
  local rule = self
  local impl = {}
  impl.neg = neg
  impl.thenpart = thenpart
  impl.ispart = ispart
  table.insert( rule.imps, impl )
  return impl
end

-------------------------------------------------------------------------------
-- Method to add a new rule to a fuzzy sistem
-- @param self The fuzzy system
-- @param weight The weight of the rule
-- @param connmethod The connection method. (must be: 'andmethod' or 'ormethod')
-- @return The rule's table
-------------------------------------------------------------------------------
local function addrule( self, weight, connmethod )
  local fis = self
  local rule = {}
  rule.weight = weight
  rule.connmethod = connmethod
  rule.pres = {}
  rule.imps = {}
  rule.addpremise = addpremise
  rule.addimplic = addimplic
  table.insert( fis.rules, rule )
  return rule
end

-------------------------------------------------------------------------------
-- Create a new fuzzy system
-- @return A new table with the fuzzy system
-------------------------------------------------------------------------------
function luafuzzy()
  -- create new table
  local fuzzy = {}
  
  -- and method
  fuzzy.andmethod = tmin
  
  -- or method
  fuzzy.ormethod = tmax
  
  -- implication method
  fuzzy.implicmethod = tmin
  
  -- aggregation method
  fuzzy.aggregmethod = tmax
  
  -- deffuzification method
  fuzzy.defuzzmethod = centroid
  
  -- step used to compute a discrete fuzzyset
  fuzzy.step = 0.01
  
  -- table os rules
  fuzzy.rules = {}
  
  -- table of inputs
  fuzzy.inps = {}
  
  -- tabla of outputs
  fuzzy.outs = {}
  
  -- method to add a new input
  fuzzy.addinp = addinp
  
  -- method to add a new output
  fuzzy.addout = addout
  
  -- method to add a new rule
  fuzzy.addrule = addrule
  
  -- method to solve the fuzzy inferece system
  fuzzy.solve = solvefuzzy
  
  return fuzzy
end
