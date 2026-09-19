function Math(el)
  -- Convert GitHub-friendly \lt to < for Pandoc/LaTeX.
  el.text = el.text:gsub("\\lt", "<")
  -- Remove GitHub inline-math backticks.
  if el.mathtype == "InlineMath" then
    local s = el.text
    if #s >= 2 and s:sub(1,1) == "`" and s:sub(-1) == "`" then
      el.text = s:sub(2,-2)
    end
  end

  return el
end

function CodeBlock(el)
  if el.classes:includes("math") then
    return pandoc.Para{
      pandoc.Math("DisplayMath", el.text)
    }
  end
end