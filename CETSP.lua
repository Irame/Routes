--[[
Close-Enough Traveling Salesman Problem (CETSP) Solver
SZVNS (Steiner Zone Variable Neighborhood Search) implementation

The CETSP differs from TSP in that nodes have collision radii. A single waypoint
can "satisfy" multiple nodes if it falls within all their collision radii.
This uses Steiner zones (maximal cliques of overlapping circles) and visibility-graph
routing around taboo polygons (obstacles).
]]

----------------------------------
-- Localize some globals
local ipairs, pairs, type = ipairs, pairs, type
local coroutine = coroutine
local tinsert, tremove = tinsert, tremove
local debugprofilestop = debugprofilestop
local inf = math.huge

local Routes = LibStub("AceAddon-3.0"):GetAddon("Routes")
local CETSP = {}
Routes.CETSP = CETSP

local function dbgPrint(...)
	-- Uncomment for debug output
	print(...)
end

local function dbgPrintFormat(...)
	dbgPrint(string.format(...))
end

-----------------------------------------------------
-- Coroutine code to allow background pathing

local CETSPUpdateFrame = CreateFrame("Frame")
CETSPUpdateFrame.running = false

function CETSPUpdateFrame:OnUpdate(elapsed)
	local status, path, meta, shortestPathLength, stageIters, timetaken = coroutine.resume(self.co)
	if status then
		if coroutine.status(self.co) == "dead" then
			-- Function finished, return results
			self:SetScript("OnUpdate", nil)
			self.running = false
			self.finishFunc(path, meta, shortestPathLength, stageIters, timetaken)
			self.finishFunc = nil
			self.statusFunc = nil
			self.co = nil
			self.nodes = nil
		end
	else
		-- An error occured in the coroutine, abort and print the error
		self:SetScript("OnUpdate", nil)
		self.running = false
		self.co = nil
		self.finishFunc = nil
		self.statusFunc = nil
		self.nodes = nil
		Routes:Print(Routes.L["The following error occured in the background path generation coroutine, please report to Grum or Xinhuan:"])
		Routes:Print(path)
	end
end

function CETSP:IsCETSPRunning()
	return CETSPUpdateFrame.running, CETSPUpdateFrame.nodes
end

-- Same arguments as CETSP:SolveCETSP(), without the "nonblocking" argument
function CETSP:SolveCETSPBackground(nodes, meta, radius, taboos, zoneID, parameters, path)
	if not CETSPUpdateFrame.running then
		CETSPUpdateFrame.co = coroutine.create(CETSP.SolveCETSP)
		CETSPUpdateFrame:SetScript("OnUpdate", CETSPUpdateFrame.OnUpdate)
		CETSPUpdateFrame.running = true
		CETSPUpdateFrame.nodes = nodes
		local status = coroutine.resume(CETSPUpdateFrame.co, CETSP, nodes, meta, radius, taboos, zoneID, parameters, path, true)
		if status then
			-- Do nothing, path isn't complete because at least 1 yield() is called.
			return 1
		else
			-- An error occured in the coroutine, abort and return the error message.
			CETSPUpdateFrame.running = false
			CETSPUpdateFrame:SetScript("OnUpdate", nil)
			CETSPUpdateFrame.co = nil
			return 3, path
		end
	else
		-- There is already a CETSP running
		return 2
	end
end

function CETSP:SetFinishFunction(func)
	assert(type(func) == "function", "SetFinishFunction() expected function in 1st argument, got "..type(func).." instead.")
	CETSPUpdateFrame.finishFunc = func
end

function CETSP:SetStatusFunction(func)
	assert(type(func) == "function", "SetStatusFunction() expected function in 1st argument, got "..type(func).." instead.")
	CETSPUpdateFrame.statusFunc = func
end

--------------------------------
-- Background execution

local nextYield = 0
local function yield()
	if not CETSPUpdateFrame.running then return end

	local t = debugprofilestop()
	if t > nextYield then
		nextYield = t + 30
		coroutine.yield()
	elseif t < nextYield then
		-- Someone called debugprofilestart(), we need to reset our timer, yield anyway
		nextYield = t + 30
		coroutine.yield()
	end
end

local function setStatus(stage, passCount, progress, pathLength)
	if CETSPUpdateFrame.running then
		if CETSPUpdateFrame.statusFunc then
			CETSPUpdateFrame.statusFunc(stage, passCount, progress, pathLength)
		end
		yield()
	end
end

---------------------------------
-- Geometry Utilities
---------------------------------

-- Calculate distance between two points {x, y}
local function dist(a, b)
	local dx = a.x - b.x
	local dy = a.y - b.y
	return sqrt(dx * dx + dy * dy)
end

-- Check if two circles intersect (including touching)
local function circlesIntersect(a, b)
	return dist(a, b) < a.r + b.r - 1e-9
end

-- Ray-casting point-in-polygon test
local function pointInPolygon(p, poly)
	local n = #poly
	local inside = false

	for i = 1, n do
		local j = (i == 1) and n or (i - 1)
		local xi, yi = poly[i].x, poly[i].y
		local xj, yj = poly[j].x, poly[j].y

		if ((yi > p.y) ~= (yj > p.y)) and
		   (p.x < (xj - xi) * (p.y - yi) / (yj - yi) + xi) then
			inside = not inside
		end
	end
	return inside
end

-- Segment AB vs segment CD strict intersection (excludes endpoints)
local function segmentsIntersect(ax, ay, bx, by, cx, cy, dx, dy)
	local d1x = bx - ax
	local d1y = by - ay
	local d2x = dx - cx
	local d2y = dy - cy
	local cross = d1x * d2y - d1y * d2x

	if abs(cross) < 1e-10 then return false end

	local t = ((cx - ax) * d2y - (cy - ay) * d2x) / cross
	local u = ((cx - ax) * d1y - (cy - ay) * d1x) / cross
	return t > 1e-9 and t < 1 - 1e-9 and u > 1e-9 and u < 1 - 1e-9
end

-- Does segment AB cross any edge of polygon?
local function segmentCrossesPolygon(ax, ay, bx, by, poly)
	local n = #poly

	for i = 1, n do
		local j = (i == n) and 1 or (i + 1)
		local c, d = poly[i], poly[j]
		if segmentsIntersect(ax, ay, bx, by, c.x, c.y, d.x, d.y) then
			return true
		end
	end
	return false
end

-- Calculate total path length from array of points
local function pathLength(pts)
	local len = 0
	for i = 2, #pts do
		len = len + dist(pts[i - 1], pts[i])
	end
	return len
end

-- Convex hull using Graham scan
local function convexHull(pts)
	local p = {}
	for _, pt in ipairs(pts) do
		tinsert(p, pt)
	end

	table.sort(p, function(a, b)
		if a.x ~= b.x then return a.x < b.x end
		return a.y < b.y
	end)

	local cross = function(O, A, B)
		return (A.x - O.x) * (B.y - O.y) - (A.y - O.y) * (B.x - O.x)
	end

	local lower = {}
	for _, q in ipairs(p) do
		while #lower >= 2 and cross(lower[#lower - 1], lower[#lower], q) <= 0 do
			tremove(lower)
		end
		tinsert(lower, q)
	end

	local upper = {}
	for i = #p, 1, -1 do
		local q = p[i]
		while #upper >= 2 and cross(upper[#upper - 1], upper[#upper], q) <= 0 do
			tremove(upper)
		end
		tinsert(upper, q)
	end

	tremove(upper)
	tremove(lower)

	for _, pt in ipairs(upper) do
		tinsert(lower, pt)
	end
	return lower
end

-- Expand polygon outward by margin
local function expandPoly(pts, margin)
	local cx = 0
	local cy = 0
	for _, p in ipairs(pts) do
		cx = cx + p.x
		cy = cy + p.y
	end
	cx = cx / #pts
	cy = cy / #pts

	local result = {}
	for _, p in ipairs(pts) do
		local dx = p.x - cx
		local dy = p.y - cy
		local d = sqrt(dx * dx + dy * dy) or 1
		tinsert(result, {
			x = p.x + dx / d * margin,
			y = p.y + dy / d * margin
		})
	end
	return result
end

-- Test if segment AB is free of taboo polygons (using original polygons)
local function segmentFree(ax, ay, bx, by, taboos)
	if not taboos then return true end

	for _, poly in ipairs(taboos) do
		if segmentCrossesPolygon(ax, ay, bx, by, poly) then
			return false
		end
		-- Mid-point inside polygon means segment passes through it
		local mx = (ax + bx) / 2
		local my = (ay + by) / 2
		if pointInPolygon({x = mx, y = my}, poly) then
			return false
		end
	end
	return true
end

---------------------------------
-- Visibility Graph Routing
---------------------------------

-- Route a segment from point A to B, avoiding taboo polygons
local function routeSegment(from, to, taboos)
	-- Fast path: straight line is clear
	if segmentFree(from.x, from.y, to.x, to.y, taboos) then
		return {from, to}
	end

	if not taboos or #taboos == 0 then
		return {from, to}
	end

	-- Build visibility graph
	local nodes = {from, to}
	local hullSets = {}

	for _, poly in ipairs(taboos) do
		local hull = convexHull(poly)
		local expanded = expandPoly(hull, 6)
		tinsert(hullSets, expanded)
		for _, v in ipairs(expanded) do
			tinsert(nodes, v)
		end
	end

	local N = #nodes
	-- Build adjacency matrix
	local adj = {}
	for i = 1, N do
		adj[i] = {}
		for j = 1, N do
			adj[i][j] = (i == j) and 0 or inf
		end
	end

	for i = 1, N do
		for j = i + 1, N do
			local a = nodes[i]
			local b = nodes[j]
			if segmentFree(a.x, a.y, b.x, b.y, taboos) then
				local d = dist(a, b)
				adj[i][j] = d
				adj[j][i] = d
			end
		end
	end

	-- Dijkstra's algorithm from node 1 to node 2
	local D = {}
	local prev = {}
	local visited = {}
	for i = 1, N do
		D[i] = inf
		prev[i] = -1
		visited[i] = false
	end
	D[1] = 0

	for _ = 1, N do
		local u = -1
		local best = inf
		for i = 1, N do
			if not visited[i] and D[i] < best then
				best = D[i]
				u = i
			end
		end
		if u == -1 or u == 2 then break end
		visited[u] = true
		for v = 1, N do
			if not visited[v] and adj[u][v] < inf then
				local nd = D[u] + adj[u][v]
				if nd < D[v] then
					D[v] = nd
					prev[v] = u
				end
			end
		end
	end

	-- Reconstruct path
	if D[2] == inf then
		return {from, to} -- No route found, use straight line
	end

	local path = {}
	local cur = 2
	while cur ~= -1 do
		tinsert(path, nodes[cur])
		cur = prev[cur]
	end

	-- Reverse to get correct order
	local reversed = {}
	for i = #path, 1, -1 do
		tinsert(reversed, path[i])
	end
	return reversed
end

-- Build full routed path for all waypoint-to-waypoint edges
local function buildRoutedPath(wps, taboos)
	if not wps or #wps < 2 then return {} end

	local segs = {}
	local n = #wps
	for i = 1, n do
		local next_i = (i == n) and 1 or (i + 1)
		tinsert(segs, routeSegment(wps[i], wps[next_i], taboos))
	end
	return segs
end

-- Calculate routed tour length
local function routedTourLen(segs)
	local len = 0
	for _, seg in ipairs(segs) do
		len = len + pathLength(seg)
	end
	return len
end

---------------------------------
-- Steiner Zone Computation
---------------------------------

-- Find a feasible intersection point of circles using iterative projection
local function feasibleIntersectionPoint(circles)
	if #circles == 0 then return nil end

	-- Start at centroid
	local p = {x = 0, y = 0}
	for _, c in ipairs(circles) do
		p.x = p.x + c.x
		p.y = p.y + c.y
	end
	p.x = p.x / #circles
	p.y = p.y / #circles

	-- Iteratively project onto circles
	for _ = 1, 60 do
		local moved = false
		for _, c in ipairs(circles) do
			local dc = dist(p, c)
			if dc > c.r + 1e-9 then
				local t = c.r / dc
				p = {x = c.x + (p.x - c.x) * t, y = c.y + (p.y - c.y) * t}
				moved = true
			end
		end
		if not moved then break end
	end

	-- Verify all circles are satisfied
	for _, c in ipairs(circles) do
		if dist(p, c) > c.r + 1e-6 then
			return nil
		end
	end

	return p
end

-- Compute Steiner zones (maximal cliques of overlapping circles)
local function computeSteinerZones(nodeList)
	local n = #nodeList
	local assigned = {}
	local zones = {}

	for i = 1, n do
		assigned[i] = false
	end

	-- Find maximal cliques
	for i = 1, n do
		if not assigned[i] then
			local groupIdxs = {i}
			local groupCircles = {nodeList[i]}
			local expanded = true

			while expanded do
				expanded = false
				for j = 1, n do
					if not assigned[j] then
						local alreadyInGroup = false
						for _, idx in ipairs(groupIdxs) do
							if idx == j then
								alreadyInGroup = true
								break
							end
						end

						if not alreadyInGroup then
							-- Check if j intersects all circles in group
							local intersectsAll = true
							for _, c in ipairs(groupCircles) do
								if not circlesIntersect(c, nodeList[j]) then
									intersectsAll = false
									break
								end
							end

							if intersectsAll then
								-- Try to add j to the group
								local candidate = {}
								for _, c in ipairs(groupCircles) do
									tinsert(candidate, c)
								end
								tinsert(candidate, nodeList[j])

								if feasibleIntersectionPoint(candidate) ~= nil then
									tinsert(groupIdxs, j)
									tinsert(groupCircles, nodeList[j])
									expanded = true
								end
							end
						end
					end
				end
			end

			if #groupIdxs > 1 then
				for _, idx in ipairs(groupIdxs) do
					assigned[idx] = true
				end
				local rep = feasibleIntersectionPoint(groupCircles)
				tinsert(zones, {
					nodeIdxs = groupIdxs,
					circles = groupCircles,
					rep = rep,
					isSingle = false
				})
			end
		end
	end

	-- Add unassigned nodes as single zones
	for i = 1, n do
		if not assigned[i] then
			local c = nodeList[i]
			tinsert(zones, {
				nodeIdxs = {i},
				circles = {c},
				rep = {x = c.x, y = c.y},
				isSingle = true
			})
		end
	end

	return zones
end

---------------------------------
-- Waypoint Optimization
---------------------------------

-- Optimize a waypoint position for a Steiner zone between prev and next points
local function bisectWaypoint(zone, prev, next)
	local mid = {x = (prev.x + next.x) / 2, y = (prev.y + next.y) / 2}
	local p = {x = mid.x, y = mid.y}

	-- Project onto circles
	for _, c in ipairs(zone.circles) do
		local dc = dist(p, c)
		if dc > c.r then
			local t = c.r / dc
			p = {x = c.x + (p.x - c.x) * t, y = c.y + (p.y - c.y) * t}
		end
	end

	-- Verify feasibility, otherwise use representative point
	local feasible = true
	for _, c in ipairs(zone.circles) do
		if dist(p, c) > c.r + 1e-6 then
			feasible = false
			break
		end
	end
	if not feasible then
		p = {x = zone.rep.x, y = zone.rep.y}
	end

	-- Gradient descent with projection
	for _ = 1, 100 do
		local d1 = dist(prev, p)
		local d2 = dist(next, p)
		local gx = 0
		local gy = 0

		if d1 > 1e-9 then
			gx = gx + (p.x - prev.x) / d1
			gy = gy + (p.y - prev.y) / d1
		end
		if d2 > 1e-9 then
			gx = gx + (p.x - next.x) / d2
			gy = gy + (p.y - next.y) / d2
		end

		local gl = sqrt(gx * gx + gy * gy)
		if gl < 1e-9 then break end

		local np = {x = p.x - gx / gl * 1.5, y = p.y - gy / gl * 1.5}

		-- Project back onto circles
		for _, c in ipairs(zone.circles) do
			local dc = dist(np, c)
			if dc > c.r then
				local t = c.r / dc
				np = {x = c.x + (np.x - c.x) * t, y = c.y + (np.y - c.y) * t}
			end
		end

		p = np
	end

	return p
end

-- Optimize waypoints for a given zone order
local function optimizeWaypoints(order, zones, maxPasses)
	maxPasses = maxPasses or 8

	if not order or #order == 0 then return {} end

	local n = #order
	local wps = {}
	for _, i in ipairs(order) do
		tinsert(wps, {x = zones[i].rep.x, y = zones[i].rep.y})
	end

	for _ = 1, maxPasses do
		local moved = false
		for i = 1, n do
			local prev_i = (i == 1) and n or (i - 1)
			local next_i = (i == n) and 1 or (i + 1)

			local prev = wps[prev_i]
			local next = wps[next_i]
			local np = bisectWaypoint(zones[order[i]], prev, next)

			if dist(np, wps[i]) > 0.05 then
				wps[i] = np
				moved = true
			end
		end
		if not moved then break end
	end

	return wps
end

---------------------------------
-- Tour Utilities
---------------------------------

-- Calculate tour length considering routing
local function wpsTourLen(wps, taboos)
	if not wps or #wps < 2 then return 0 end

	if not taboos or #taboos == 0 then
		local len = 0
		for i = 1, #wps do
			local next_i = (i == #wps) and 1 or (i + 1)
			len = len + dist(wps[i], wps[next_i])
		end
		return len
	end

	return routedTourLen(buildRoutedPath(wps, taboos))
end

---------------------------------
-- Tour Construction and Improvement
---------------------------------

-- Build nearest neighbor tour
local function buildNNTour(zones)
	local n = #zones
	if n == 0 then return {} end

	local visited = {}
	local order = {1}
	visited[1] = true

	while #order < n do
		local last = order[#order]
		local best = -1
		local bestD = inf

		for i = 1, n do
			if not visited[i] then
				local d = dist(zones[last].rep, zones[i].rep)
				if d < bestD then
					bestD = d
					best = i
				end
			end
		end

		visited[best] = true
		tinsert(order, best)
	end

	return order
end

--[[
Optimized twoOpt for CETSP.lua
Guided by TSP.lua's TwoOpt implementation (TSP:TwoOpt).

Key improvements over the original CETSP twoOpt:
  1. Reverse-lookup table (orderR) — O(1) position lookup instead of O(n) scan.
  2. Neighbor pruning — only test (i,j) pairs where zone j is geometrically close
     to zone i (like TSP's prune[] table), skipping hopeless candidates.
  3. In-place segment reversal — reverses order[i+1..j] with a two-pointer swap
     instead of allocating a brand-new table for every candidate pair.
  4. Cheap delta pre-filter — uses rep-point distances (straight-line heuristic)
     to discard candidates before paying the cost of optimizeWaypoints/wpsTourLen.
  5. Waypoint re-optimization only on acceptance — optimizeWaypoints is called
     only when the swap is actually kept, not for every (i,j) pair.
  6. b/z update after swap — like TSP, the inner loop refreshes its edge
     immediately after a successful swap so further checks in the same pass
     are consistent.

Drop-in replacement for the existing `twoOpt` local function in CETSP.lua.
All external call sites (order, wps = twoOpt(order, wps, steinerZones, cetspTaboos))
remain unchanged.
]]

-- Build a neighbor-prune list for each zone index.
-- Two zones are "neighbors" if their representative points are closer than
-- `pruneRadius`. When pruneRadius is nil the function falls back to a
-- fraction of the bounding-box diagonal so it works without tuning.
local function buildPruneList(zones, pruneRadius)
    local n = #zones

    if not pruneRadius then
        -- Compute bounding box of rep points and use 30 % of the diagonal.
        local minX, minY, maxX, maxY = math.huge, math.huge, -math.huge, -math.huge
        for _, z in ipairs(zones) do
            if z.rep.x < minX then minX = z.rep.x end
            if z.rep.y < minY then minY = z.rep.y end
            if z.rep.x > maxX then maxX = z.rep.x end
            if z.rep.y > maxY then maxY = z.rep.y end
        end
        local diag = sqrt((maxX - minX)^2 + (maxY - minY)^2)
        pruneRadius = diag * 0.30
    end

    local prune = {}
    for i = 1, n do
        prune[i] = {}
    end

    for i = 1, n do
        for j = i + 1, n do
            local dx = zones[i].rep.x - zones[j].rep.x
            local dy = zones[i].rep.y - zones[j].rep.y
            if dx * dx + dy * dy < pruneRadius * pruneRadius then
                tinsert(prune[i], j)
                tinsert(prune[j], i)
            end
        end
    end

    return prune
end

-- Straight-line distance between the rep points of two zones by index.
-- Used for the cheap delta pre-filter (no taboo routing overhead).
local function repDist(zones, a, b)
    local dx = zones[a].rep.x - zones[b].rep.x
    local dy = zones[a].rep.y - zones[b].rep.y
    return sqrt(dx * dx + dy * dy)
end

-- 2-opt tour improvement for CETSP.
-- Signature matches the original: (order, wps, zones, taboos) -> order, wps
local function twoOpt(order, wps, zones, taboos)
    local n = #order
    if n < 4 then return order, wps end

    -- Build neighbor-prune list (analogous to TSP's prune[] table).
    local prune = buildPruneList(zones)

    -- Reverse-lookup: orderR[zoneIdx] = position in order[] (like TSP's pathR).
    local orderR = {}
    for pos = 1, n do
        orderR[order[pos]] = pos
    end

    -- Current best tour length (used for acceptance threshold).
    local bestLen = wpsTourLen(wps, taboos)

    local improved = true
    local iters    = 0

    while improved and iters < 40 do
        dbgPrint("[CETSP] 2-opt iteration " .. iters)
        improved = false
        iters    = iters + 1

        for i = 1, n - 1 do
            local zi   = order[i]
            local zi1  = order[i + 1]

            -- Cheap edge cost from rep-points for the pre-filter.
            local edgeAB = repDist(zones, zi, zi1)

            -- Only iterate over pruned neighbors of zi (like TSP's inner loop).
            for _, zj in ipairs(prune[zi]) do
                local j = orderR[zj]

                -- Standard 2-opt validity:
                --   j must exist in order (guard nil from orderR miss),
                --   j must be strictly after i+1 (no adjacent edge),
                --   j must be < n so that order[j+1] is always valid
                --   (the wrap-around edge i=1,j=n is also excluded by j < n).
                if j and j > i + 1 and j < n then
                    local zj1 = order[j + 1]  -- safe: j < n guarantees j+1 <= n

                    -- ── Cheap delta pre-filter (rep-point heuristic) ────────
                    -- Current edges: (zi → zi1) + (zj → zj1)
                    -- Proposed edges: (zi → zj)  + (zi1 → zj1)
                    -- Only proceed if the proposed pair is shorter by at
                    -- least a small margin (avoids paying optimizeWaypoints
                    -- for obviously bad swaps).
                    local edgeCD     = repDist(zones, zj, zj1)
                    local proposedAC = repDist(zones, zi, zj)
                    local proposedBD = repDist(zones, zi1, zj1)

                    if proposedAC + proposedBD < edgeAB + edgeCD - 0.1 then
                        -- ── In-place segment reversal (like TSP) ─────────────
                        -- Reverse order[i+1 .. j] and keep orderR in sync.
                        local left  = i + 1
                        local right = j
                        while left < right do
                            local L, R = order[left], order[right]
                            order[left],  order[right]  = R, L
                            orderR[L], orderR[R] = right, left
                            left  = left  + 1
                            right = right - 1
                        end

                        -- ── CETSP-specific acceptance check ──────────────────
                        -- Now that zone order is reversed we re-optimise
                        -- waypoints and measure the true routed length.
                        local newWps = optimizeWaypoints(order, zones, 4)
                        local newLen = wpsTourLen(newWps, taboos)

                        if newLen < bestLen - 0.5 then
                            -- Accept the swap.
                            wps     = newWps
                            bestLen = newLen
                            improved = true

                            -- Refresh the edge reference for the outer loop
                            -- (mirrors TSP's `b = path[i+1]; z = weight[...]`).
                            zi1   = order[i + 1]
                            edgeAB = repDist(zones, zi, zi1)
                        else
                            -- Reject: undo the reversal.
                            left  = i + 1
                            right = j
                            while left < right do
                                local L, R = order[left], order[right]
                                order[left],  order[right]  = R, L
                                orderR[L], orderR[R] = right, left
                                left  = left  + 1
                                right = right - 1
                            end
                            -- zi1 / edgeAB are still valid after undo.
                        end
                    end
                end

            end

			setStatus(3, iters, i/(n-1), bestLen)
        end

    end

    return order, wps, iters
end

--[[
Optimized reinsert (Reinsertion VNS) for CETSP.lua
Guided by TSP.lua's TwoOpt / 2.5-opt (TSP:TwoOpt twoPointFiveOpt branch).

Problems with the original reinsert():
  1. First-improvement exit — returns on the first gain found, forcing the
     outer VNS loop to restart a full O(n²) scan from scratch each time.
  2. No pruning — every (i,j) pair is tested regardless of spatial distance.
  3. Full table allocation per candidate — builds a brand-new newOrder table
     before any cost check.
  4. Double wpsTourLen call per candidate — wps baseline is recomputed
     inside the loop even though it doesn't change between candidates.
  5. Only single-zone (Or-1) moves — Or-2 and Or-3 segment moves are much
     stronger for CETSP where adjacent zones are spatially coupled.

What this version does instead (guided by TSP:TwoOpt 2.5-opt branch):
  1. Best-improvement within each full pass — collects all improving moves,
     applies the best one per pass, then restarts; never exits early.
  2. Neighbor pruning (reuses buildPruneList from twoOpt) — only tests
     insertion targets j that are geometrically close to zone i, mirroring
     TSP's prune[] table in the 2.5-opt inner loop.
  3. Reverse-lookup (orderR) — O(1) position queries, same as TSP's pathR.
  4. Clean remove+insert (applyReinsertion) — two explicit branches
     (insertAfter < from vs > segEnd) with simple sequential copies;
     verified correct by unit tests for Or-1/2/3 in both directions.
  5. Cheap rep-point delta pre-filter — screens out obviously bad moves
     before paying for optimizeWaypoints / wpsTourLen.
  6. Or-1, Or-2, Or-3 segment moves — moves chains of 1, 2, or 3 consecutive
     zones; Or-2/3 extend TSP's 2.5-opt to longer segments.
  7. Baseline length cached outside all loops — computed once per pass.

Drop-in replacement for the existing `reinsert` local function in CETSP.lua.
Call site in SolveCETSP is unchanged:
  local newOrder, newWps, improved = reinsert(order, wps, steinerZones, cetspTaboos)

NOTE: buildPruneList and repDist must be defined before this function.
      They are already present after the twoOpt optimisation (twoOpt_optimized.lua).
]]

-- Build a new order table by removing the segment [from .. from+segLen-1]
-- and reinserting it after position insertAfter (in the original ordering).
-- Two explicit branches handle leftward vs rightward moves.
-- Verified correct by unit tests for Or-1, Or-2, Or-3 in both directions.
local function applyReinsertion(order, from, segLen, insertAfter)
    local n      = #order
    local segEnd = from + segLen - 1
    local result = {}

    if insertAfter < from then
        -- Segment moves LEFT: insert before its current position.
        -- New layout: [1..insertAfter] [seg] [insertAfter+1..from-1] [segEnd+1..n]
        for k = 1, insertAfter do
            result[#result + 1] = order[k]
        end
        for k = from, segEnd do
            result[#result + 1] = order[k]
        end
        for k = insertAfter + 1, from - 1 do
            result[#result + 1] = order[k]
        end
        for k = segEnd + 1, n do
            result[#result + 1] = order[k]
        end
    else
        -- Segment moves RIGHT: insertAfter > segEnd.
        -- New layout: [1..from-1] [segEnd+1..insertAfter] [seg] [insertAfter+1..n]
        for k = 1, from - 1 do
            result[#result + 1] = order[k]
        end
        for k = segEnd + 1, insertAfter do
            result[#result + 1] = order[k]
        end
        for k = from, segEnd do
            result[#result + 1] = order[k]
        end
        for k = insertAfter + 1, n do
            result[#result + 1] = order[k]
        end
    end

    return result
end

-- Cheap rep-point delta for moving segment [from..segEnd] to after insertAfter.
-- Returns (added_edges - removed_edges): negative means improvement.
local function orKDelta(order, zones, from, segLen, insertAfter)
    local n      = #order
    local segEnd = from + segLen - 1

    local function rep(pos)
        return zones[order[((pos - 1) % n) + 1]].rep
    end

    local function d(a, b)
        local dx = a.x - b.x
        local dy = a.y - b.y
        return sqrt(dx * dx + dy * dy)
    end

    -- Three edges broken: pred(from)->from, segEnd->succ(segEnd), insertAfter->succ(insertAfter)
    -- Three edges added:  pred(from)->succ(segEnd), insertAfter->from, segEnd->succ(insertAfter)
    local predFrom   = rep(from - 1)
    local repFrom    = rep(from)
    local repSegEnd  = rep(segEnd)
    local succSegEnd = rep(segEnd + 1)
    local repInsert  = rep(insertAfter)
    local succInsert = rep(insertAfter + 1)

    local removed = d(predFrom,  repFrom)
                  + d(repSegEnd, succSegEnd)
                  + d(repInsert, succInsert)

    local added   = d(predFrom,  succSegEnd)
                  + d(repInsert, repFrom)
                  + d(repSegEnd, succInsert)

    return added - removed
end

-- Optimized reinsertion VNS.
-- Performs Or-1, Or-2, Or-3 moves with neighbor pruning and best-improvement
-- selection within each pass.
-- Returns: newOrder, newWps, improved (bool)
local function reinsert(order, wps, zones, taboos)
    local n = #order
    if n < 4 then return order, wps, false end

    -- Reverse-lookup: orderR[zoneIdx] = current position in order[].
    -- Mirrors TSP's pathR used in the 2.5-opt branch.
    local orderR = {}
    for pos = 1, n do
        orderR[order[pos]] = pos
    end

    -- Neighbor-prune list: reuses buildPruneList from twoOpt_optimized.lua.
    local prune = buildPruneList(zones)

    -- Cache baseline tour length — computed once per pass, not per candidate.
    local bestLen     = wpsTourLen(wps, taboos)

    -- Outer loop: repeat passes until no improvement found in a full pass.
    local passImproved = true
	local passCount = 0
    while passImproved do
		passCount = passCount + 1
        passImproved = false

        -- Track the single best move found across the whole pass.
        local bestDelta    = -0.5   -- minimum improvement threshold (yards)
        local bestNewOrder = nil
        local bestNewWps   = nil
        local bestNewLen   = nil

        -- Or-k for segment lengths 1, 2, 3.
        for segLen = 1, 3 do
            if n < segLen + 2 then break end

            for i = 1, n do
                local segEnd = i + segLen - 1
                if segEnd > n then break end  -- no wrap-around segments

                local zi = order[i]

                -- Inner loop over pruned neighbors of the segment head,
                -- exactly like TSP's `for m = 1, #prune[a]` in 2.5-opt.
                for _, zj in ipairs(prune[zi]) do
                    local j = orderR[zj]

                    -- Validity guards:
                    --   j must exist (nil guard for zones not in order)
                    --   j must not overlap [i-1 .. segEnd] (no adjacent/overlap)
                    --   skip trivial no-op wrap (i=1, j=n)
                    if j and
                       (j < i - 1 or j > segEnd) and
                       not (j == n and i == 1) then

                        -- Cheap rep-point pre-filter before paying for
                        -- optimizeWaypoints / wpsTourLen.
                        local delta = orKDelta(order, zones, i, segLen, j)
                        if delta < bestDelta then
                            local candOrder = applyReinsertion(order, i, segLen, j)
                            local candWps   = optimizeWaypoints(candOrder, zones, 4)
                            local candLen   = wpsTourLen(candWps, taboos)

                            if candLen < bestLen + bestDelta then
                                bestDelta    = candLen - bestLen
                                bestNewOrder = candOrder
                                bestNewWps   = candWps
                                bestNewLen   = candLen
                            end
                        end
                    end
                end

				if i % 5 == 0 then
            		setStatus(4, passCount, ((segLen-1)*n+i)/(3*n))
				end
            end
        end

        -- Apply the best move found in this pass.
        if bestNewOrder then
            order        = bestNewOrder
            wps          = bestNewWps
            bestLen      = bestNewLen
            passImproved = true

            -- Rebuild reverse-lookup to reflect the new order.
            for pos = 1, n do
                orderR[order[pos]] = pos
            end

			setStatus(4, passCount, 1, bestLen)

            dbgPrintFormat("[CETSP] VNS reinsert: new len %.2f (delta %.2f)", bestLen, bestDelta)
        end
    end

    return order, wps, passCount
end

-----------------------------------
-- CETSP:SolveCETSP(nodes, radius, taboos, zoneID, parameters, path, nonblocking)
-- Arguments
--   nodes       - The table containing a list of Routes node IDs to path
--                 This list should only contain nodes on the same map. This
--                 table should be indexed numerically from nodes[1] to nodes[n].
--   radius      - The neighborhood radius in yards to use for the CETSP. Nodes whose collision circles intersect can be satisfied by a single waypoint.
--   taboos      - A table containing a table of taboo regions to use.
--   zoneID      - The map area ID of the map that the route is to be generated on.
--   parameters  - The table containing the ACO parameters to use.
--   path        - An optional input table that is used to supply the result
--                 table. If this is nil, the function returns a new table.
--   nonblocking - A boolean to indicate whether the function should yield() regularly.
-- Returns
--   path        - The result CETSP path is a table indexed numerically from path[1]
--                 to path[n], a list of Routes node IDs.
--   metadata    - The table containing the cluster metadata, if available
--   length      - The length in yards of the path returned.
--   iteration   - Number of interations taken.
--   timeTaken   - Number of seconds used.
-- Notes: A new nodes[] and metadata[] table is returned. The original tables
--        sent in are unmodified.
function CETSP:SolveCETSP(nodes, metadata, radius, taboos, zoneID, parameters, path, nonblocking)
	-- Notes: Some of these code might look convoluted, with seemingly unnecessary use of too many locals
	-- and make the code look longer. But they are for speed optimization.
	assert(type(nodes) == "table", "SolveCETSP() expected table in 1st argument, got "..type(nodes).." instead.")
	assert(not metadata or type(metadata) == "table", "SolveCETSP() expected table in 2nd argument, got "..type(metadata).." instead.")
	assert(type(radius) == "number", "SolveCETSP() expected number in 3rd argument, got "..type(radius).." instead.")
	assert(type(taboos) == "table", "SolveCETSP() expected table in 4th argument, got "..type(taboos).." instead.")
	assert(type(parameters) == "table", "SolveCETSP() expected table in 6th argument, got "..type(parameters).." instead.")
	if type(path) == "table" then
		wipe(path)
	else
		path = {}
	end

	if nonblocking then
		-- Ensure that at least 1 yield() is called in a nonblocking call
		coroutine.yield()
	end

	-- Setup ACO parameters
	local startTime
	if nonblocking then
		startTime = GetTime()
	else
		startTime = debugprofilestop()
	end

	if metadata then
		nodes = {}
		local num = 0
		for i = 1, #metadata do
			for j = 1, #metadata[i] do
				num = num+1
				nodes[num] = metadata[i][j]
			end
		end
	end

	local cetspNodes = {}
	local zoneW, zoneH = Routes.Dragons:GetZoneSize(zoneID)
	for _, nodeID in ipairs(nodes) do
		local x, y = Routes:getXY(nodeID)
		tinsert(cetspNodes, {x = x * zoneW, y = y * zoneH, r = radius})
	end

	local cetspTaboos = {}
	for _, taboo in ipairs(taboos) do
		local cetspTaboo = {}
		for _, nodeID in ipairs(taboo.route) do
			local x, y = Routes:getXY(nodeID)
			tinsert(cetspTaboo, {x = x * zoneW, y = y * zoneH})
		end
		tinsert(cetspTaboos, cetspTaboo)
	end

	local stageIters = {}
	local passCount

	-- Stage 1: Compute Steiner zones
	local steinerZones = computeSteinerZones(cetspNodes)
	dbgPrintFormat("[CETSP] Computed %d Steiner zones", #steinerZones)

	if #steinerZones == 0 then
		dbgPrint("[CETSP] No zones found, returning empty result")
		return path, 0, 0, 0
	end

	-- Stage 2: Build nearest neighbor tour
	yield()
	local order = buildNNTour(steinerZones)
	local wps = optimizeWaypoints(order, steinerZones, parameters.maxPasses or 10)
	local initLen = wpsTourLen(wps, cetspTaboos)
	dbgPrintFormat("[CETSP] Built NN tour with length %.2f", initLen)

	-- Stage 3: 2-opt improvement
	yield()
	local beforeOpt = wpsTourLen(wps, cetspTaboos)
	order, wps, passCount = twoOpt(order, wps, steinerZones, cetspTaboos)
	stageIters[3] = passCount
	local afterOpt = wpsTourLen(wps, cetspTaboos)
	dbgPrintFormat("[CETSP] 2-opt: %.2f -> %.2f", beforeOpt, afterOpt)

	-- Stage 4: Reinsertion VNS
	yield()
	order, wps, passCount = reinsert(order, wps, steinerZones, cetspTaboos)
	stageIters[4] = passCount

	-- Stage 5: Final optimization
	wps = optimizeWaypoints(order, steinerZones, parameters.maxPasses or 10)
	local segments = buildRoutedPath(wps, cetspTaboos)
	local tourLen = routedTourLen(segments)
	local timeTaken
	if nonblocking then
		timeTaken = GetTime() - startTime
	else
		timeTaken = (debugprofilestop() - startTime) / 1000
	end

	dbgPrintFormat("[CETSP] Final tour length: %.2f (%.3f s)", tourLen, timeTaken)

	-- Convert segments back to node IDs
	for _, seg in ipairs(segments) do
		local x = seg[1].x / zoneW
		local y = seg[1].y / zoneH
		tinsert(path, Routes:getID(x, y))
	end

	-- Create metadata
	local metadata = {}
	for i, zoneIdx in ipairs(order) do
		local zone = steinerZones[zoneIdx]

		local cluster = {}
		for _, nodeIdx in ipairs(zone.nodeIdxs) do
			local nodeID = nodes[nodeIdx]
			tinsert(cluster, nodeID)
		end
		tinsert(metadata, cluster)
	end

	return path, metadata, tourLen, stageIters, timeTaken
end

-----------------------------------
-- CETSP:InsertNode(nodes, metadata, zoneID, nodeID, radius, taboos)
-- Arguments
--   nodes       - The table containing a list of Routes node IDs to path
--                 This list should only contain nodes on the same map. This
--                 table should be indexed numerically from nodes[1] to nodes[n].
--   metadata    - The table containing the zone cluster metadata, if available
--   zoneID      - The map area ID of the map that the route is on.
--   nodeID      - The Routes node ID to insert into the route.
--   radius      - The neighborhood radius in yards for the CETSP.
--   taboos      - The taboo polygon table (same format as SolveCETSP). May be nil.
-- Returns
--   pathLength  - The routed CETSP tour length in yards (consistent with SolveCETSP).
-- Notes: This function modifies the original nodes[] and metadata[] tables
--        directly. It performs minimal computation by greedily inserting
--        the new node into an existing zone (if overlapping) or as a new zone,
--        then runs a local 2-opt pass over the edges adjacent to the insertion
--        to restore local optimality.
function CETSP:InsertNode(nodes, metadata, zoneID, nodeID, radius, taboos)
	assert(type(nodes) == "table", "InsertNode() expected table in 1st argument, got "..type(nodes).." instead.")

	local numNodes = #nodes
	if numNodes == 0 then
		tinsert(nodes, nodeID)
		if metadata then
			tinsert(metadata, {nodeID})
		end
		dbgPrint("[CETSP:InsertNode] Trivial case (0 nodes): added first node")
		return 0
	end

	if numNodes < 3 then
		-- For 1-2 existing nodes the tour has no meaningful geometry yet;
		-- just append the new zone and let the caller re-solve when ready.
		tinsert(nodes, nodeID)
		if metadata then
			tinsert(metadata, {nodeID})
		end
		dbgPrintFormat("[CETSP:InsertNode] Trivial case: added node to zone (numNodes=%d)", numNodes)
		return 0
	end

	-- Get zone dimensions for coordinate conversion
	local zoneW, zoneH = Routes.Dragons:GetZoneSize(zoneID)

	-- Convert taboos to CETSP coordinate space once here so every internal
	-- routing call receives the real obstacles.
	local cetspTaboos = {}
	if taboos then
		for _, taboo in ipairs(taboos) do
			local cetspTaboo = {}
			for _, tabooNodeID in ipairs(taboo.route) do
				local x, y = Routes:getXY(tabooNodeID)
				tinsert(cetspTaboo, {x = x * zoneW, y = y * zoneH})
			end
			tinsert(cetspTaboos, cetspTaboo)
		end
	end

	-- Helper: build a CETSP circle table from a metadata cluster (list of node IDs)
	local function getMetaCircles(nodeList)
		local circles = {}
		for _, nid in ipairs(nodeList) do
			local x, y = Routes:getXY(nid)
			tinsert(circles, {x = x * zoneW, y = y * zoneH, r = radius})
		end
		return circles
	end

	-- Helper: build a zone structure from a circle list
	local function buildZoneFromCircles(circles)
		local rep = feasibleIntersectionPoint(circles) or {x = circles[1].x, y = circles[1].y}
		return {
			circles  = circles,
			rep      = rep,
			isSingle = (#circles == 1),
			-- nodeIdxs not needed here; we track cluster membership via metadata[]
		}
	end

	-- Helper: rebuild the full zone + order arrays from the current metadata table.
	local function buildAllZoneStructures()
		local zones = {}
		local order = {}
		for i = 1, #metadata do
			tinsert(zones, buildZoneFromCircles(getMetaCircles(metadata[i])))
			tinsert(order, i)
		end
		return zones, order
	end

	-- Optimize waypoints, route through taboos, compute tour length, then atomically
	-- rebuild nodes[] from the accepted solution so nodes and metadata stay in sync.
	-- Returns the routed tour length in yards.
	local function finalizeZones(zones, order)
		local finalWps = optimizeWaypoints(order, zones, 8)
		local segs = buildRoutedPath(finalWps, cetspTaboos)
		local tourLen = routedTourLen(segs)

		wipe(nodes)
		for _, seg in ipairs(segs) do
			local x = seg[1].x / zoneW
			local y = seg[1].y / zoneH
			tinsert(nodes, Routes:getID(x, y))
		end

		-- Reorder metadata to match the tour order so metadata[i] always
		-- corresponds to nodes[i] after localTwoOpt may have permuted order[].
		local reorderedMeta = {}
		for _, zoneIdx in ipairs(order) do
			reorderedMeta[#reorderedMeta + 1] = metadata[zoneIdx]
		end
		wipe(metadata)
		for _, cluster in ipairs(reorderedMeta) do
			metadata[#metadata + 1] = cluster
		end

		return tourLen
	end

	-- 2-opt pass restricted to edges touching insertedPos and its immediate neighbors.
	-- Only the edges adjacent to the new zone can benefit from a swap involving it,
	-- so this covers the useful candidates in O(n) comparisons instead of O(n^2).
	local function localTwoOpt(zones, order, insertedPos)
		local n = #order
		if n < 4 then return order end

		-- An edge index i represents the edge from order[i] to order[i+1 mod n].
		local function edgeIdx(pos)
			return ((pos - 1) % n) + 1
		end

		-- Collect the three edges that touch insertedPos (prev, self, next).
		local candidates = {}
		local seen = {}
		for delta = -1, 1 do
			local e = edgeIdx(insertedPos + delta)
			if not seen[e] then
				seen[e] = true
				tinsert(candidates, e)
			end
		end

		local wps = optimizeWaypoints(order, zones, 4)
		local bestLen = wpsTourLen(wps, cetspTaboos)
		local improved = true

		while improved do
			improved = false
			for _, i in ipairs(candidates) do
				-- Test swapping candidate edge i with every other non-adjacent edge j.
				for j = i + 2, n - 1 do
					-- Cheap rep-point pre-filter before paying for optimizeWaypoints.
					local zi   = order[i]
					local zi1  = order[(i % n) + 1]
					local zj   = order[j]
					local zj1  = order[(j % n) + 1]
					local curCost  = repDist(zones, zi, zi1) + repDist(zones, zj, zj1)
					local propCost = repDist(zones, zi, zj)  + repDist(zones, zi1, zj1)
					if propCost < curCost - 0.1 then
						-- Reverse order[i+1..j] in place and test the new tour length.
						local left, right = i + 1, j
						while left < right do
							order[left], order[right] = order[right], order[left]
							left = left + 1; right = right - 1
						end
						local newWps = optimizeWaypoints(order, zones, 4)
						local newLen = wpsTourLen(newWps, cetspTaboos)
						if newLen < bestLen - 0.5 then
							wps     = newWps
							bestLen = newLen
							improved = true
						else
							-- Reject: undo the reversal.
							left, right = i + 1, j
							while left < right do
								order[left], order[right] = order[right], order[left]
								left = left + 1; right = right - 1
							end
						end
					end
				end
			end
		end

		return order, wps, bestLen
	end

	-- Convert new node to CETSP format
	local newX, newY = Routes:getXY(nodeID)
	local newCircle = {x = newX * zoneW, y = newY * zoneH, r = radius}
	dbgPrintFormat("[CETSP:InsertNode] Inserting node at (%.2f, %.2f) with radius %.0f", newX, newY, radius)

	-- -------------------------------------------------------------------------
	-- Main insertion logic
	-- -------------------------------------------------------------------------
	if metadata and #metadata > 0 then

		-- Find which existing zones the new node's circle overlaps.
		local overlappingZones = {}
		for zoneIdx, cluster in ipairs(metadata) do
			for _, clusterNodeID in ipairs(cluster) do
				local x, y = Routes:getXY(clusterNodeID)
				local circle = {x = x * zoneW, y = y * zoneH, r = radius}
				if circlesIntersect(circle, newCircle) then
					tinsert(overlappingZones, zoneIdx)
					break
				end
			end
		end
		dbgPrintFormat("[CETSP:InsertNode] Found %d overlapping zone(s)", #overlappingZones)

		-- ------------------------------------------------------------------
		-- Case A: New node overlaps exactly one existing zone.
		-- Ungroup that zone, recompute Steiner sub-zones, splice them back
		-- into the tour at the same position the original zone occupied.
		-- ------------------------------------------------------------------
		if #overlappingZones == 1 then
			local zoneIdx = overlappingZones[1]

			-- Collect all nodes from the overlapping zone plus the new node.
			local ungroupedNodes = {}
			for _, clusterNodeID in ipairs(metadata[zoneIdx]) do
				tinsert(ungroupedNodes, clusterNodeID)
			end
			tinsert(ungroupedNodes, nodeID)

			-- Remove the old zone; nodes[] will be fully rebuilt by finalizeZones.
			tremove(metadata, zoneIdx)

			-- Recompute Steiner zones for the ungrouped pool.
			local cetspNodes = {}
			for _, node_id in ipairs(ungroupedNodes) do
				local x, y = Routes:getXY(node_id)
				tinsert(cetspNodes, {x = x * zoneW, y = y * zoneH, r = radius})
			end
			local newSteinerZones = computeSteinerZones(cetspNodes)

			-- Splice sub-zones back at zoneIdx, preserving relative sub-zone order.
			-- Inserting at the original position gives optimizeWaypoints a spatially
			-- sensible starting tour rather than a degenerate appended one.
			for subIdx, zone in ipairs(newSteinerZones) do
				local zoneNodeIDs = {}
				for _, nodeIdx in ipairs(zone.nodeIdxs) do
					tinsert(zoneNodeIDs, ungroupedNodes[nodeIdx])
				end
				table.insert(metadata, zoneIdx + subIdx - 1, zoneNodeIDs)
			end

			local zones, order = buildAllZoneStructures()
			order, _, _ = localTwoOpt(zones, order, zoneIdx)
			local tourLen = finalizeZones(zones, order)

			dbgPrintFormat("[CETSP:InsertNode] Ungrouped zone %d -> %d sub-zones; tour=%.2f", zoneIdx, #newSteinerZones, tourLen)
			return tourLen

		-- ------------------------------------------------------------------
		-- Case B: New node overlaps multiple existing zones.
		-- Merge all their nodes plus the new node into one pool, recompute
		-- Steiner zones, then find the best insertion position for each
		-- sub-zone using the rep-point delta heuristic. One final
		-- optimizeWaypoints pass is done after all positions are committed.
		-- ------------------------------------------------------------------
		elseif #overlappingZones > 1 then
			-- The lowest tour index among the removed zones serves as the anchor
			-- for re-inserting sub-zones so they land near their original position.
			local anchorIdx = overlappingZones[1]  -- already sorted ascending

			-- Collect all nodes from every overlapping zone plus the new node.
			local ungroupedNodes = {}
			for _, zoneIdx in ipairs(overlappingZones) do
				for _, clusterNodeID in ipairs(metadata[zoneIdx]) do
					tinsert(ungroupedNodes, clusterNodeID)
				end
			end
			tinsert(ungroupedNodes, nodeID)

			-- Remove overlapping zones in reverse order to keep indices valid.
			for i = #overlappingZones, 1, -1 do
				tremove(metadata, overlappingZones[i])
			end
			-- Adjust anchorIdx for the zones that were removed before it.
			local removedBefore = 0
			for _, zi in ipairs(overlappingZones) do
				if zi < anchorIdx then removedBefore = removedBefore + 1 end
			end
			anchorIdx = anchorIdx - removedBefore
			if anchorIdx < 1 then anchorIdx = 1 end

			-- Recompute Steiner zones for the ungrouped pool.
			local cetspNodes = {}
			for _, node_id in ipairs(ungroupedNodes) do
				local x, y = Routes:getXY(node_id)
				tinsert(cetspNodes, {x = x * zoneW, y = y * zoneH, r = radius})
			end
			local newSteinerZones = computeSteinerZones(cetspNodes)

			-- For each new sub-zone, find the best insertion position using only
			-- the O(1) rep-point delta, accumulating results into a local table.
			-- metadata is not touched until all positions are decided so it is
			-- never left in a partially updated state.
			local insertedMetadata = {}
			for i = 1, #metadata do
				tinsert(insertedMetadata, metadata[i])
			end

			for subIdx, zone in ipairs(newSteinerZones) do
				local zoneNodeIDs = {}
				for _, nodeIdx in ipairs(zone.nodeIdxs) do
					tinsert(zoneNodeIDs, ungroupedNodes[nodeIdx])
				end

				-- Rebuild temp zone list to account for sub-zones already placed.
				local tempZones = {}
				for i = 1, #insertedMetadata do
					tinsert(tempZones, buildZoneFromCircles(getMetaCircles(insertedMetadata[i])))
				end

				local nTemp     = #tempZones
				local bestPos   = anchorIdx + subIdx - 1  -- seed near the anchor
				local bestDelta = math.huge

				for pos = 1, nTemp + 1 do
					local prevIdx = (pos - 2) % nTemp + 1
					local nextIdx = (pos - 1) % nTemp + 1
					local prevRep = tempZones[prevIdx].rep
					local nextRep = tempZones[nextIdx].rep

					local dx1 = prevRep.x - nextRep.x
					local dy1 = prevRep.y - nextRep.y
					local removed = sqrt(dx1*dx1 + dy1*dy1)

					local dx2 = prevRep.x - zone.rep.x
					local dy2 = prevRep.y - zone.rep.y
					local dx3 = zone.rep.x - nextRep.x
					local dy3 = zone.rep.y - nextRep.y
					local added = sqrt(dx2*dx2 + dy2*dy2) + sqrt(dx3*dx3 + dy3*dy3)

					local delta = added - removed
					if delta < bestDelta then
						bestDelta = delta
						bestPos   = pos
					end
				end

				table.insert(insertedMetadata, bestPos, zoneNodeIDs)
			end

			-- All positions decided; atomically replace metadata contents.
			wipe(metadata)
			for i = 1, #insertedMetadata do
				tinsert(metadata, insertedMetadata[i])
			end

			local zones, order = buildAllZoneStructures()
			order, _, _ = localTwoOpt(zones, order, anchorIdx)
			local tourLen = finalizeZones(zones, order)

			dbgPrintFormat("[CETSP:InsertNode] Merged %d overlapping zones -> %d sub-zones; tour=%.2f", #overlappingZones, #newSteinerZones, tourLen)
			return tourLen

		-- ------------------------------------------------------------------
		-- Case C: No overlap — insert as a brand-new single-node zone.
		-- Pick the tour gap with the rep-point delta heuristic, then use
		-- bisectWaypoint to place the initial waypoint relative to its
		-- neighbors rather than at the raw node coordinate.
		-- ------------------------------------------------------------------
		else
			local newZoneStruct = {
				circles  = {newCircle},
				rep      = {x = newCircle.x, y = newCircle.y},
				isSingle = true,
			}

			local existingZones = {}
			for i = 1, #metadata do
				tinsert(existingZones, buildZoneFromCircles(getMetaCircles(metadata[i])))
			end

			local n = #existingZones
			local bestPos  = n + 1
			local minDelta = math.huge

			for pos = 1, n + 1 do
				local prevIdx = (pos - 2) % n + 1
				local nextIdx = (pos - 1) % n + 1
				local prevRep = existingZones[prevIdx].rep
				local nextRep = existingZones[nextIdx].rep

				local dx1 = prevRep.x - nextRep.x
				local dy1 = prevRep.y - nextRep.y
				local removed = sqrt(dx1*dx1 + dy1*dy1)

				local dx2 = prevRep.x - newZoneStruct.rep.x
				local dy2 = prevRep.y - newZoneStruct.rep.y
				local dx3 = newZoneStruct.rep.x - nextRep.x
				local dy3 = newZoneStruct.rep.y - nextRep.y
				local added = sqrt(dx2*dx2 + dy2*dy2) + sqrt(dx3*dx3 + dy3*dy3)

				local delta = added - removed
				if delta < minDelta then
					minDelta = delta
					bestPos  = pos
				end
			end

			dbgPrintFormat("[CETSP:InsertNode] No-overlap: inserting new zone at position %d (delta=%.2f)", bestPos, minDelta)

			table.insert(metadata, bestPos, {nodeID})

			-- Build the full zone list with the new entry included, then run
			-- bisectWaypoint once to seed the waypoint relative to its neighbors
			-- before optimizeWaypoints refines all positions together.
			local zones, order = buildAllZoneStructures()
			local prevPos = (bestPos - 2) % #zones + 1
			local nextPos = bestPos % #zones + 1
			local prevWp  = {x = zones[order[prevPos]].rep.x, y = zones[order[prevPos]].rep.y}
			local nextWp  = {x = zones[order[nextPos]].rep.x, y = zones[order[nextPos]].rep.y}
			bisectWaypoint(zones[order[bestPos]], prevWp, nextWp)

			order, _, _ = localTwoOpt(zones, order, bestPos)
			local tourLen = finalizeZones(zones, order)

			dbgPrintFormat("[CETSP:InsertNode] Created new zone at position %d; tour=%.2f", bestPos, tourLen)
			return tourLen
		end

	else
		-- No metadata available: just append and return.
		-- Without zone structures we cannot do CETSP routing, so the returned
		-- length is a TSP approximation only.
		tinsert(nodes, nodeID)
		dbgPrint("[CETSP:InsertNode] No metadata, added to simple node list")
		return Routes.TSP:PathLength(nodes, zoneID)
	end
end

-----------------------------------
-- CETSP:DeleteNode(nodes, metadata, zoneID, coord, radius)
-- Arguments
--   nodes       - The table containing a list of Routes node IDs to path
--                 This list should only contain nodes on the same map. This
--                 table should be indexed numerically from nodes[1] to nodes[n].
--   metadata    - The table containing the zone cluster metadata, if available
--   zoneID      - The map area ID of the map that the route is on.
--   coord       - The Routes coordinate ID of the node to delete.
-- Returns
--   found       - Boolean indicating whether the node was found and deleted.
-- Notes: This function modifies the original nodes[] and metadata[] tables
--        directly. When a node is deleted from a zone with multiple nodes,
--        the zone remains valid. When the last node is removed, the zone is deleted.
function CETSP:DeleteNode(nodes, metadata, zoneID, coord)
	assert(type(nodes) == "table", "DeleteNode() expected table in 1st argument, got "..type(nodes).." instead.")

	dbgPrintFormat("[CETSP:DeleteNode] Attempting to delete coord=%s, zoneID=%d, metadata=%s", tostring(coord), zoneID, metadata and "yes" or "no")

	-- Search for the node in metadata zones
	if metadata and #metadata > 0 then
		dbgPrintFormat("[CETSP:DeleteNode] Searching in %d metadata zones", #metadata)
		for i = 1, #metadata do
			for j = 1, #metadata[i] do
				if coord == metadata[i][j] then
					-- Found the node in zone i
					dbgPrintFormat("[CETSP:DeleteNode] Found node in zone %d at position %d (zone has %d nodes)", i, j, #metadata[i])
					if #metadata[i] > 1 then
						-- More than 1 node in this zone: just remove the node
						tremove(metadata[i], j)
						dbgPrintFormat("[CETSP:DeleteNode] Removed node from zone %d (now has %d nodes)", i, #metadata[i])
					else
						-- Only 1 node in this zone: remove the entire zone and the correspondsing node
						tremove(metadata, i)
						tremove(nodes, i)
						dbgPrintFormat("[CETSP:DeleteNode] Removed entire zone %d (zone had only 1 node)", i)
					end

					return true
				end
			end
		end
		dbgPrint("[CETSP:DeleteNode] Node not found in any metadata zone")
	else
		-- No metadata: simple node list, just remove the node
		dbgPrint("[CETSP:DeleteNode] No metadata available, searching in simple node list")
		for i = 1, #nodes do
			if coord == nodes[i] then
				tremove(nodes, i)
				dbgPrintFormat("[CETSP:DeleteNode] Removed node from simple list at position %d", i)
				return true
			end
		end
		dbgPrint("[CETSP:DeleteNode] Node not found in simple node list")
	end

	dbgPrint("[CETSP:DeleteNode] Deletion failed - node not found")
	return false
end

-- vim: ts=4 noexpandtab
