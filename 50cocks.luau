local S = {}
S.NoRecoil = {}
S.NoRecoil.Settings = {}
S.NoRecoil.Settings.GunMods = {}
S.NoRecoil.Settings.GunMods.NoRecoil = true
S.NoRecoil.Settings.GunMods.NoSpread = true

local function cacheWeapons_NR()
    S.NoRecoil.WeaponCache = {}
    for _, v in pairs(getgc(true)) do
        if type(v) == 'table' and rawget(v, 'EquipTime') then
            table.insert(S.NoRecoil.WeaponCache, v)
            if not S.NoRecoil.OriginalValues[v] then
                S.NoRecoil.OriginalValues[v] = {
                    Recoil = v.Recoil,
                    CameraRecoilingEnabled = v.CameraRecoilingEnabled,
                    AngleX_Min = v.AngleX_Min,
                    AngleX_Max = v.AngleX_Max,
                    AngleY_Min = v.AngleY_Min,
                    AngleY_Max = v.AngleY_Max,
                    AngleZ_Min = v.AngleZ_Min,
                    AngleZ_Max = v.AngleZ_Max,
                    Spread = v.Spread
                }
            end
        end
    end
end

local function applyGunMods_NR()
    for _, weapon in ipairs(S.NoRecoil.WeaponCache) do
        if S.NoRecoil.Settings.GunMods.NoRecoil then
            weapon.Recoil = 0
            weapon.CameraRecoilingEnabled = false
            weapon.AngleX_Min = 0
            weapon.AngleX_Max = 0
            weapon.AngleY_Min = 0
            weapon.AngleY_Max = 0
            weapon.AngleZ_Min = 0
            weapon.AngleZ_Max = 0
        end
        if S.NoRecoil.Settings.GunMods.Spread then
            weapon.Spread = S.NoRecoil.Settings.GunMods.SpreadAmount
        end
    end
end

local function resetGunMods_NR()
    for weapon, values in pairs(S.NoRecoil.OriginalValues) do
        if weapon then
            pcall(function()
                weapon.Recoil = values.Recoil
                weapon.CameraRecoilingEnabled = values.CameraRecoilingEnabled
                weapon.AngleX_Min = values.AngleX_Min
                weapon.AngleX_Max = values.AngleX_Max
                weapon.AngleY_Min = values.AngleY_Min
                weapon.AngleY_Max = values.AngleY_Max
                weapon.AngleZ_Min = values.AngleZ_Min
                weapon.AngleZ_Max = values.AngleZ_Max
                weapon.Spread = values.Spread
            end)
        end
    end
end

local function handleWeapon_NR(weapon)
    if S.NoRecoil.Enabled then
        task.wait(0.1)
        cacheWeapons_NR()
        applyGunMods_NR()
    end
end

local function onCharacterAdded_NR(character)
    for _, child in ipairs(character:GetChildren()) do
        if child:IsA("Tool") then
            handleWeapon_NR(child)
        end
    end
    
    local childConn = character.ChildAdded:Connect(function(child)
        if child:IsA("Tool") then
            handleWeapon_NR(child)
        end
    end)
    table.insert(S.NoRecoil.Connections, childConn)
    
    local humanoid = character:WaitForChild("Humanoid", 2)
    if humanoid then
        local diedConn = humanoid.Died:Connect(function()
            if S.NoRecoil.Enabled then
                task.wait(1.5)
                cacheWeapons_NR()
                applyGunMods_NR()
            end
        end)
        table.insert(S.NoRecoil.Connections, diedConn)
    end
end

local LP = game:GetService("Players").LocalPlayer

local function enableNoRecoil()
    if S.NoRecoil.Enabled then return end
    S.NoRecoil.Enabled = true
    S.NoRecoil.WeaponCache = {}
    S.NoRecoil.OriginalValues = {}
    
    cacheWeapons_NR()
    applyGunMods_NR()
    
    local charConn = LP.CharacterAdded:Connect(onCharacterAdded_NR)
    table.insert(S.NoRecoil.Connections, charConn)
    
    if LP.Character then
        onCharacterAdded_NR(LP.Character)
    end
end

local function disableNoRecoil()
    if not S.NoRecoil.Enabled then return end
    S.NoRecoil.Enabled = false
    
    resetGunMods_NR()
    
    for _, conn in ipairs(S.NoRecoil.Connections) do
        conn:Disconnect()
    end
    S.NoRecoil.Connections = {}
end

local blah = {}
blah.toggle = function(state, norecoil, nospread)
    if norecoil then
        S.NoRecoil.Settings.GunMods.NoRecoil = norecoil
    end
    if nospread then
        S.NoRecoil.Settings.GunMods.NoSpread = nospread
    end
    if state then
        enableNoRecoil()
    else
        disableNoRecoil()
    end
end

return blah
