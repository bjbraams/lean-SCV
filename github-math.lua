function Math(el)
  if el.mathtype == "InlineMath" then
    local s = el.text
    if #s >= 2 and s:sub(1,1) == "`" and s:sub(-1) == "`" then
      el.text = s:sub(2,-2)
    end
  end
  return el
end
