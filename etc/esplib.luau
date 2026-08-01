--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.9) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 59) then
					if (Enum <= 29) then
						if (Enum <= 14) then
							if (Enum <= 6) then
								if (Enum <= 2) then
									if (Enum <= 0) then
										Stk[Inst[2]][Inst[3]] = Inst[4];
									elseif (Enum > 1) then
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										local T = Stk[A];
										for Idx = A + 1, Top do
											Insert(T, Stk[Idx]);
										end
									end
								elseif (Enum <= 4) then
									if (Enum > 3) then
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									else
										Stk[Inst[2]] = {};
									end
								elseif (Enum == 5) then
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum <= 10) then
								if (Enum <= 8) then
									if (Enum > 7) then
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									else
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									end
								elseif (Enum == 9) then
									local A = Inst[2];
									local Index = Stk[A];
									local Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								else
									local A = Inst[2];
									local T = Stk[A];
									for Idx = A + 1, Inst[3] do
										Insert(T, Stk[Idx]);
									end
								end
							elseif (Enum <= 12) then
								if (Enum == 11) then
									Stk[Inst[2]] = Inst[3];
								else
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum == 13) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 26) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 21) then
							if (Enum <= 17) then
								if (Enum <= 15) then
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								elseif (Enum == 16) then
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 19) then
								if (Enum == 18) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 20) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 25) then
							if (Enum <= 23) then
								if (Enum > 22) then
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
								else
									local A = Inst[2];
									local C = Inst[4];
									local CB = A + 2;
									local Result = {Stk[A](Stk[A + 1], Stk[CB])};
									for Idx = 1, C do
										Stk[CB + Idx] = Result[Idx];
									end
									local R = Result[1];
									if R then
										Stk[CB] = R;
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum > 24) then
								do
									return;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 27) then
							if (Enum == 26) then
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Stk[Inst[2]] <= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 28) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 44) then
						if (Enum <= 36) then
							if (Enum <= 32) then
								if (Enum <= 30) then
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 31) then
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 34) then
								if (Enum == 33) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									do
										return Stk[A], Stk[A + 1];
									end
								end
							elseif (Enum == 35) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 40) then
							if (Enum <= 38) then
								if (Enum > 37) then
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum == 39) then
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 42) then
							if (Enum > 41) then
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum == 43) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum <= 51) then
						if (Enum <= 47) then
							if (Enum <= 45) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 46) then
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 49) then
							if (Enum == 48) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum > 50) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						else
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 55) then
						if (Enum <= 53) then
							if (Enum == 52) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum == 54) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 57) then
						if (Enum > 56) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						elseif (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 58) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					end
				elseif (Enum <= 89) then
					if (Enum <= 74) then
						if (Enum <= 66) then
							if (Enum <= 62) then
								if (Enum <= 60) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								elseif (Enum == 61) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum <= 64) then
								if (Enum == 63) then
									Stk[Inst[2]] = not Stk[Inst[3]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								end
							elseif (Enum > 65) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								do
									return;
								end
							end
						elseif (Enum <= 70) then
							if (Enum <= 68) then
								if (Enum > 67) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum == 69) then
								Stk[Inst[2]] = not Stk[Inst[3]];
							else
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							end
						elseif (Enum <= 72) then
							if (Enum == 71) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum == 73) then
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						else
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Top do
								Insert(T, Stk[Idx]);
							end
						end
					elseif (Enum <= 81) then
						if (Enum <= 77) then
							if (Enum <= 75) then
								VIP = Inst[3];
							elseif (Enum > 76) then
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 79) then
							if (Enum > 78) then
								do
									return Stk[Inst[2]];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum == 80) then
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						else
							local A = Inst[2];
							local Cls = {};
							for Idx = 1, #Lupvals do
								local List = Lupvals[Idx];
								for Idz = 0, #List do
									local Upv = List[Idz];
									local NStk = Upv[1];
									local DIP = Upv[2];
									if ((NStk == Stk) and (DIP >= A)) then
										Cls[DIP] = NStk[DIP];
										Upv[1] = Cls;
									end
								end
							end
						end
					elseif (Enum <= 85) then
						if (Enum <= 83) then
							if (Enum == 82) then
								local A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 84) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 26) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 87) then
						if (Enum > 86) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum == 88) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					end
				elseif (Enum <= 104) then
					if (Enum <= 96) then
						if (Enum <= 92) then
							if (Enum <= 90) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							elseif (Enum > 91) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							end
						elseif (Enum <= 94) then
							if (Enum == 93) then
								if (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 95) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 100) then
						if (Enum <= 98) then
							if (Enum > 97) then
								if (Stk[Inst[2]] <= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								VIP = Inst[3];
							end
						elseif (Enum > 99) then
							local A = Inst[2];
							local Cls = {};
							for Idx = 1, #Lupvals do
								local List = Lupvals[Idx];
								for Idz = 0, #List do
									local Upv = List[Idz];
									local NStk = Upv[1];
									local DIP = Upv[2];
									if ((NStk == Stk) and (DIP >= A)) then
										Cls[DIP] = NStk[DIP];
										Upv[1] = Cls;
									end
								end
							end
						else
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 102) then
						if (Enum > 101) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						end
					elseif (Enum == 103) then
						local B = Stk[Inst[4]];
						if not B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					end
				elseif (Enum <= 112) then
					if (Enum <= 108) then
						if (Enum <= 106) then
							if (Enum == 105) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum == 107) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 110) then
						if (Enum == 109) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum > 111) then
						Stk[Inst[2]] = {};
					else
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					end
				elseif (Enum <= 116) then
					if (Enum <= 114) then
						if (Enum == 113) then
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum == 115) then
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					elseif (Inst[2] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 118) then
					if (Enum == 117) then
						Stk[Inst[2]] = #Stk[Inst[3]];
					else
						local B = Stk[Inst[4]];
						if B then
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = B;
							VIP = Inst[3];
						end
					end
				elseif (Enum > 119) then
					local A = Inst[2];
					local Step = Stk[A + 2];
					local Index = Stk[A] + Step;
					Stk[A] = Index;
					if (Step > 0) then
						if (Index <= Stk[A + 1]) then
							VIP = Inst[3];
							Stk[A + 3] = Index;
						end
					elseif (Index >= Stk[A + 1]) then
						VIP = Inst[3];
						Stk[A + 3] = Index;
					end
				else
					Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!7E3Q0003043Q0067616D65030A3Q0047657453657276696365030A3Q0052756E5365727669636503073Q00506C617965727303093Q00576F726B737061636503113Q005265706C69636174656453746F72616765030B3Q004C6F63616C506C61796572030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503083Q00496E7374616E63652Q033Q006E657703063Q00466F6C64657203063Q0067657468756903073Q00436F726547756903043Q006D61746803053Q00666C2Q6F7203053Q00726F756E6403053Q006174616E322Q033Q0073696E2Q033Q00636F7303053Q007461626C6503053Q00636C65617203063Q00756E7061636B03043Q0066696E6403143Q00576F726C64546F56696577706F7274506F696E742Q033Q0049734103083Q004765745069766F74030E3Q0046696E6446697273744368696C6403153Q0046696E6446697273744368696C644F66436C612Q73030B3Q004765744368696C6472656E03063Q00434672616D6503083Q006964656E74697479030D3Q00546F4F7269656E746174696F6E03123Q00506F696E74546F4F626A656374537061636503063Q00436F6C6F723303043Q004C65727003073Q00566563746F723203043Q007A65726F2Q033Q004D696E2Q033Q004D617803073Q00566563746F7233026Q001440028Q00026Q000840026Q00F03F027Q0040026Q00F0BF03073Q002Q5F696E64657803093Q00436F6E73747275637403063Q0063726561746503083Q00446573747275637403063Q0055706461746503063Q0052656E646572030A3Q005F6861734C6F616465640100030C3Q005F6F626A656374436163686503093Q0077686974656C697374030E3Q0073686172656453652Q74696E6773030C3Q006E6F6E506C6179657245535003083Q007465787453697A65026Q002A4003083Q0074657874466F6E74030D3Q006C696D697444697374616E6365030B3Q006D617844697374616E6365025Q00C06240030C3Q007465616D53652Q74696E677303053Q00656E656D7903073Q00656E61626C65642Q012Q033Q00626F7803083Q00626F78436F6C6F72030A3Q00626F784F75746C696E65030F3Q00626F784F75746C696E65436F6C6F7203073Q00626F7846692Q6C030C3Q00626F7846692Q6C436F6C6F72026Q00E03F03093Q006865616C7468426172030C3Q006865616C746879436F6C6F72030A3Q006479696E67436F6C6F7203103Q006865616C74684261724F75746C696E6503153Q006865616C74684261724F75746C696E65436F6C6F72030A3Q006865616C746854657874030F3Q006865616C746854657874436F6C6F7203113Q006865616C7468546578744F75746C696E6503163Q006865616C7468546578744F75746C696E65436F6C6F7203053Q00626F783364030A3Q00626F783364436F6C6F7203043Q006E616D6503093Q006E616D65436F6C6F72030B3Q006E616D654F75746C696E6503103Q006E616D654F75746C696E65436F6C6F7203063Q00776561706F6E030B3Q00776561706F6E436F6C6F72030D3Q00776561706F6E4F75746C696E6503123Q00776561706F6E4F75746C696E65436F6C6F7203083Q0064697374616E6365030D3Q0064697374616E6365436F6C6F72030F3Q0064697374616E63654F75746C696E6503143Q0064697374616E63654F75746C696E65436F6C6F7203063Q00747261636572030C3Q007472616365724F726967696E03063Q004D692Q646C65030B3Q00747261636572436F6C6F72030D3Q007472616365724F75746C696E6503123Q007472616365724F75746C696E65436F6C6F72030E3Q006F2Q665363722Q656E412Q726F7703133Q006F2Q665363722Q656E412Q726F77436F6C6F7203123Q006F2Q665363722Q656E412Q726F7753697A65026Q00394003143Q006F2Q665363722Q656E412Q726F7752616469757303153Q006F2Q665363722Q656E412Q726F774F75746C696E65031A3Q006F2Q665363722Q656E412Q726F774F75746C696E65436F6C6F7203053Q006368616D7303103Q006368616D7356697369626C654F6E6C79030E3Q006368616D7346692Q6C436F6C6F72029A5Q99C93F03113Q006368616D734F75746C696E65436F6C6F7203083Q00667269656E646C79026Q006440030B3Q00412Q64496E7374616E6365030E3Q0055706461746553652Q74696E677303043Q004C6F616403063Q00556E6C6F616403093Q00676574576561706F6E030A3Q006973467269656E646C7903093Q006765744865616C746800AF022Q00126D3Q00013Q0020665Q000200120B000200034Q00533Q0002000200126D000100013Q00206600010001000200120B000300044Q005300010003000200126D000200013Q00206600020002000200120B000400054Q005300020004000200126D000300013Q00206600030003000200120B000500064Q005300030005000200206B00040001000700206B00050002000800206B00060005000900126D0007000A3Q00206B00070007000B00120B0008000C3Q00126D0009000D3Q0006100009001D00013Q00044B3Q001D000100126D0009000D4Q003D00090001000200065C000900210001000100044B3Q0021000100126D000900013Q00206600090009000200120B000B000E4Q00530009000B00022Q005300070009000200126D0008000F3Q00206B00080008001000126D0009000F3Q00206B00090009001100126D000A000F3Q00206B000A000A001200126D000B000F3Q00206B000B000B001300126D000C000F3Q00206B000C000C001400126D000D00153Q00206B000D000D001600126D000E00153Q00206B000E000E001700126D000F00153Q00206B000F000F001800206B00100005001900206B00110002001A00206B00120002001B00206B00130002001C00206B00140002001D00206B00150002001E00126D0016001F3Q00206B00160016002000206B00160016002100126D0017001F3Q00206B00170017002000206B00170017002200126D001800233Q00206B00180018000B2Q003D00180001000200206B00180018002400126D001900253Q00206B00190019002600206B00190019002700126D001A00253Q00206B001A001A002600206B001A001A002800126D001B00253Q00206B001B001B002600206B001B001B002400126D001C00293Q00206B001C001C002600206B001C001C002700126D001D00293Q00206B001D001D002600206B001D001D002800126D001E00253Q00206B001E001E000B00120B001F002A3Q00120B0020002B4Q0053001E0020000200126D001F00253Q00206B001F001F000B00120B0020002C3Q00120B0021002B4Q0053001F0021000200126D002000253Q00206B00200020000B00120B0021002B3Q00120B0022002D4Q005300200022000200126D002100253Q00206B00210021000B00120B0022002B3Q00120B0023002E4Q005300210023000200126D002200253Q00206B00220022000B00120B0023002B3Q00120B0024002E4Q00530022002400022Q0003002300073Q00126D002400293Q00206B00240024000B00120B0025002F3Q00120B0026002F3Q00120B0027002F4Q005300240027000200126D002500293Q00206B00250025000B00120B0026002F3Q00120B0027002D3Q00120B0028002F4Q005300250028000200126D002600293Q00206B00260026000B00120B0027002F3Q00120B0028002D3Q00120B0029002D4Q005300260029000200126D002700293Q00206B00270027000B00120B0028002F3Q00120B0029002F3Q00120B002A002D4Q00530027002A000200126D002800293Q00206B00280028000B00120B0029002D3Q00120B002A002F3Q00120B002B002F4Q00530028002B000200126D002900293Q00206B00290029000B00120B002A002D3Q00120B002B002D3Q00120B002C002F4Q00530029002C000200126D002A00293Q00206B002A002A000B00120B002B002D3Q00120B002C002D3Q00120B002D002D4Q0053002A002D000200126D002B00293Q00206B002B002B000B00120B002C002D3Q00120B002D002F3Q00120B002E002D4Q0013002B002E4Q000100233Q000100065500243Q000100012Q001A3Q00033Q00023C002500013Q00065500260002000100022Q001A3Q001C4Q001A3Q001D3Q00065500270003000100022Q001A3Q00104Q001A3Q00053Q00065500280004000100072Q001A3Q00234Q001A3Q00274Q001A3Q00194Q001A3Q00064Q001A3Q000E4Q001A3Q001A4Q001A3Q00083Q00065500290005000100022Q001A3Q000C4Q001A3Q000B4Q0003002A5Q001069002A0030002A000655002B0006000100022Q001A3Q002A4Q001A3Q00013Q001069002A000B002B000655002B0007000100012Q001A7Q001069002A0031002B00023C002B00083Q001069002A0032002B000655002B0009000100012Q001A3Q000D3Q001069002A0033002B000655002B000A000100112Q001A3Q00014Q001A3Q000F4Q001A3Q00134Q001A3Q00274Q001A3Q00154Q001A3Q000D4Q001A3Q00114Q001A3Q00254Q001A3Q00244Q001A3Q00284Q001A3Q00264Q001A3Q00164Q001A3Q00054Q001A3Q00174Q001A3Q000A4Q001A3Q000C4Q001A3Q000B3Q001069002A0034002B000655002B000B0001000C2Q001A3Q001E4Q001A3Q001B4Q001A3Q00184Q001A3Q00204Q001A3Q00094Q001A3Q001F4Q001A3Q00214Q001A3Q00224Q001A3Q00064Q001A3Q00194Q001A3Q001A4Q001A3Q00293Q001069002A0035002B2Q0003002B5Q001069002B0030002B000655002C000C000100012Q001A3Q002B3Q001069002B000B002C000655002C000D000100022Q001A3Q00074Q001A7Q001069002B0031002C000655002C000E000100012Q001A3Q000D3Q001069002B0033002C000655002C000F000100022Q001A3Q00014Q001A3Q000F3Q001069002B0034002C2Q0003002C5Q001069002C0030002C000655002D0010000100012Q001A3Q002C3Q001069002C000B002D000655002D0011000100012Q001A7Q001069002C0031002D00023C002D00123Q001069002C0033002D000655002D0013000100032Q001A3Q00124Q001A3Q00274Q001A3Q00093Q001069002C0035002D2Q0003002D3Q000500302Q002D003600372Q0003002E5Q001069002D0038002E2Q0003002E5Q001069002D0039002E2Q0003002E3Q000500302Q002E003B003700302Q002E003C003D00302Q002E003E002E00302Q002E003F003700302Q002E00400041001069002D003A002E2Q0003002E3Q00022Q0003002F3Q001C00302Q002F0044004500302Q002F004600372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002B3Q00120B0034002B4Q005300310034000200120B0032002D4Q0063003000020001001069002F0047003000302Q002F004800372Q0003003000023Q00126D003100233Q00206B00310031000B2Q003D00310001000200120B0032002D4Q0063003000020001001069002F0049003000302Q002F004A00372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002B3Q00120B0034002B4Q005300310034000200120B0032004C4Q0063003000020001001069002F004B003000302Q002F004D003700126D003000233Q00206B00300030000B00120B0031002B3Q00120B0032002D3Q00120B0033002B4Q0053003000330002001069002F004E003000126D003000233Q00206B00300030000B00120B0031002D3Q00120B0032002B3Q00120B0033002B4Q0053003000330002001069002F004F003000302Q002F005000372Q0003003000023Q00126D003100233Q00206B00310031000B2Q003D00310001000200120B0032004C4Q0063003000020001001069002F0051003000302Q002F005200372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F0053003000302Q002F0054003700126D003000233Q00206B00300030000B2Q003D003000010002001069002F0055003000302Q002F005600372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002B3Q00120B0034002B4Q005300310034000200120B0032002D4Q0063003000020001001069002F0057003000302Q002F005800372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F0059003000302Q002F005A003700126D003000233Q00206B00300030000B2Q003D003000010002001069002F005B003000302Q002F005C00372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F005D003000302Q002F005E003700126D003000233Q00206B00300030000B2Q003D003000010002001069002F005F003000302Q002F006000372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F0061003000302Q002F0062003700126D003000233Q00206B00300030000B2Q003D003000010002001069002F0063003000302Q002F0064003700302Q002F006500662Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002B3Q00120B0034002B4Q005300310034000200120B0032002D4Q0063003000020001001069002F0067003000302Q002F006800372Q0003003000023Q00126D003100233Q00206B00310031000B2Q003D00310001000200120B0032002D4Q0063003000020001001069002F0069003000302Q002F006A00372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F006B003000302Q002F006C006D00302Q002F006E004100302Q002F006F00372Q0003003000023Q00126D003100233Q00206B00310031000B2Q003D00310001000200120B0032002D4Q0063003000020001001069002F0070003000302Q002F0071003700302Q002F007200372Q0003003000023Q00126D003100233Q00206B00310031000B00120B003200743Q00120B003300743Q00120B003400744Q005300310034000200120B0032004C4Q0063003000020001001069002F007300302Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002B3Q00120B0034002B4Q005300310034000200120B0032002B4Q0063003000020001001069002F00750030001069002E0043002F2Q0003002F3Q001C00302Q002F0044004500302Q002F004600372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002B3Q00120B0033002D3Q00120B0034002B4Q005300310034000200120B0032002D4Q0063003000020001001069002F0047003000302Q002F004800372Q0003003000023Q00126D003100233Q00206B00310031000B2Q003D00310001000200120B0032002D4Q0063003000020001001069002F0049003000302Q002F004A00372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002B3Q00120B0033002D3Q00120B0034002B4Q005300310034000200120B0032004C4Q0063003000020001001069002F004B003000302Q002F004D003700126D003000233Q00206B00300030000B00120B0031002B3Q00120B0032002D3Q00120B0033002B4Q0053003000330002001069002F004E003000126D003000233Q00206B00300030000B00120B0031002D3Q00120B0032002B3Q00120B0033002B4Q0053003000330002001069002F004F003000302Q002F005000372Q0003003000023Q00126D003100233Q00206B00310031000B2Q003D00310001000200120B0032004C4Q0063003000020001001069002F0051003000302Q002F005200372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F0053003000302Q002F0054003700126D003000233Q00206B00300030000B2Q003D003000010002001069002F0055003000302Q002F005600372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002B3Q00120B0033002D3Q00120B0034002B4Q005300310034000200120B0032002D4Q0063003000020001001069002F0057003000302Q002F005800372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F0059003000302Q002F005A003700126D003000233Q00206B00300030000B2Q003D003000010002001069002F005B003000302Q002F005C00372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F005D003000302Q002F005E003700126D003000233Q00206B00300030000B2Q003D003000010002001069002F005F003000302Q002F006000372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F0061003000302Q002F0062003700126D003000233Q00206B00300030000B2Q003D003000010002001069002F0063003000302Q002F0064003700302Q002F006500662Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002B3Q00120B0033002D3Q00120B0034002B4Q005300310034000200120B0032002D4Q0063003000020001001069002F0067003000302Q002F006800372Q0003003000023Q00126D003100233Q00206B00310031000B2Q003D00310001000200120B0032002D4Q0063003000020001001069002F0069003000302Q002F006A00372Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002D3Q00120B0033002D3Q00120B0034002D4Q005300310034000200120B0032002D4Q0063003000020001001069002F006B003000302Q002F006C006D00302Q002F006E007700302Q002F006F00372Q0003003000023Q00126D003100233Q00206B00310031000B2Q003D00310001000200120B0032002D4Q0063003000020001001069002F0070003000302Q002F0071003700302Q002F007200372Q0003003000023Q00126D003100233Q00206B00310031000B00120B003200743Q00120B003300743Q00120B003400744Q005300310034000200120B0032004C4Q0063003000020001001069002F007300302Q0003003000023Q00126D003100233Q00206B00310031000B00120B0032002B3Q00120B0033002D3Q00120B0034002B4Q005300310034000200120B0032002B4Q0063003000020001001069002F00750030001069002E0076002F001069002D0042002E000655002E0014000100022Q001A3Q002D4Q001A3Q002C3Q001069002D0078002E000655002E0015000100012Q001A3Q002D3Q001069002D0079002E000655002E0016000100062Q001A3Q002D4Q001A3Q00044Q001A3Q00014Q001A3Q002A4Q001A3Q002B4Q001A3Q00023Q001069002D007A002E000655002E0017000100022Q001A3Q002D4Q001A3Q000D3Q001069002D007B002E00023C002E00183Q001069002D007C002E000655002E0019000100022Q001A3Q00014Q001A3Q00043Q001069002D007D002E000655002E001A000100012Q001A3Q00143Q001069002D007E002E2Q004F002D00024Q00193Q00013Q001B3Q00093Q0003043Q0066696E6403053Q00546F72736F030E3Q0046696E6446697273744368696C6403093Q00436861725374617473030C3Q004865616C746856616C75657303093Q0044657374726F7965642Q033Q0049734103093Q00422Q6F6C56616C756503053Q0056616C756502333Q00206600020001000100120B000400024Q00530002000400020006100002000700013Q00044B3Q000700012Q000600026Q004F000200024Q003600025Q00206600020002000300120B000400044Q005300020004000200065C0002000F0001000100044B3Q000F00012Q000600036Q004F000300023Q0020660003000200032Q001500056Q005300030005000200065C000300160001000100044B3Q001600012Q000600046Q004F000400023Q00206600040003000300120B000600054Q005300040006000200065C0004001D0001000100044B3Q001D00012Q000600056Q004F000500023Q0020660005000400032Q0015000700014Q005300050007000200065C000500240001000100044B3Q002400012Q000600066Q004F000600023Q00206600060005000300120B000800064Q00530006000800020006100006003000013Q00044B3Q0030000100206600070006000700120B000900084Q00530007000900020006100007003000013Q00044B3Q0030000100206B0007000600092Q004F000700024Q000600076Q004F000700024Q00193Q00017Q00053Q0003043Q004865616403043Q0066696E6403053Q00546F72736F2Q033Q004C65672Q033Q0041726D01143Q00265D3Q00110001000100044B3Q0011000100206600013Q000200120B000300034Q005300010003000200065C000100120001000100044B3Q0012000100206600013Q000200120B000300044Q005300010003000200065C000100120001000100044B3Q0012000100206600013Q000200120B000300054Q005300010003000200044B3Q001200012Q002F00016Q0006000100014Q004F000100024Q00193Q00017Q000A3Q00026Q00F03F03063Q00434672616D6503043Q0053697A6503083Q00506F736974696F6E026Q00E03F03073Q00566563746F72332Q033Q006E657703013Q005803013Q005903013Q005A012A3Q00120B000300014Q007500045Q00120B000500013Q0004090003001A00012Q000700073Q000600206B00080007000200206B0009000700032Q0036000A5Q000667000B000B0001000100044B3Q000B000100206B000B00080004002040000C000900052Q0077000C0008000C00206B000C000C00042Q0053000A000C00022Q00150001000A4Q0036000A00013Q000667000B00140001000200044B3Q0014000100206B000B00080004002040000C000900052Q0026000C0008000C00206B000C000C00042Q0053000A000C00022Q00150002000A3Q0004780003000400012Q002600030001000200204000030003000500126D000400063Q00206B00040004000700206B00050003000800206B00060003000900206B00070002000A2Q005300040007000200126D000500023Q00206B0005000500072Q0015000600034Q0015000700044Q00530005000700022Q00770006000200012Q0022000500034Q00193Q00017Q00053Q0003073Q00566563746F72322Q033Q006E657703013Q005803013Q005903013Q005A010D4Q003600016Q0036000200014Q001500036Q002400010003000200126D000300013Q00206B00030003000200206B00040001000300206B0005000100042Q00530003000500022Q0015000400023Q00206B0005000100052Q003A000300024Q00193Q00017Q000D3Q00026Q00F03F026Q00E03F03083Q00506F736974696F6E03073Q00566563746F723203043Q007A65726F03073Q00636F726E65727303073Q00746F704C6566742Q033Q006E657703013Q005803013Q005903083Q00746F705269676874030A3Q00626F2Q746F6D4C656674030B3Q00626F2Q746F6D526967687402494Q000300025Q00120B000300014Q003600046Q0075000400043Q00120B000500013Q0004090003001000012Q0036000700013Q0020400008000100022Q003600096Q00070009000900062Q000F0008000800092Q002600083Q000800206B0008000800032Q00140007000200022Q00590002000600070004780003000600012Q0036000300024Q0036000400034Q0036000500044Q0015000600024Q0057000500064Q001C00033Q00022Q0036000400053Q00126D000500043Q00206B0005000500052Q0036000600044Q0015000700024Q0057000600074Q001C00043Q00022Q000300053Q000500106900050006000200126D000600043Q00206B0006000600082Q0036000700063Q00206B0008000300092Q00140007000200022Q0036000800063Q00206B00090003000A2Q0057000800094Q001C00063Q000200106900050007000600126D000600043Q00206B0006000600082Q0036000700063Q00206B0008000400092Q00140007000200022Q0036000800063Q00206B00090003000A2Q0057000800094Q001C00063Q00020010690005000B000600126D000600043Q00206B0006000600082Q0036000700063Q00206B0008000300092Q00140007000200022Q0036000800063Q00206B00090004000A2Q0057000800094Q001C00063Q00020010690005000C000600126D000600043Q00206B0006000600082Q0036000700063Q00206B0008000400092Q00140007000200022Q0036000800063Q00206B00090004000A2Q0057000800094Q001C00063Q00020010690005000D00062Q004F000500024Q00193Q00017Q00053Q0003073Q00566563746F723203043Q007A65726F2Q033Q006E657703013Q005803013Q0059021A3Q00065C3Q00050001000100044B3Q0005000100126D000200013Q00206B0002000200022Q004F000200024Q003600026Q0015000300014Q00140002000200022Q0036000300014Q0015000400014Q001400030002000200126D000400013Q00206B00040004000300206B00053Q00042Q000F00050002000500206B00063Q00052Q000F0006000300062Q007700050005000600206B00063Q00042Q000F00060003000600206B00073Q00052Q000F0007000200072Q00260006000600072Q0025000400064Q003100046Q00193Q00017Q000A3Q00030C3Q007365746D6574617461626C6503093Q0063686172616374657203063Q00612Q73657274032E3Q004D692Q73696E6720617267756D656E7420233120284D6F64656C2F4368617261637465722065787065637465642903093Q00696E7465726661636503243Q004D692Q73696E6720617267756D656E7420233220287461626C652065787065637465642903053Q007063612Q6C03063Q00706C6179657203163Q00476574506C6179657246726F6D43686172616374657203093Q00436F6E737472756374021C3Q00126D000200014Q000300036Q003600046Q005300020004000200126D000300034Q001500045Q00120B000500044Q005300030005000200106900020002000300126D000300034Q0015000400013Q00120B000500064Q005300030005000200106900020005000300126D000300073Q00065500043Q000100022Q001A3Q00024Q001A3Q00014Q003B0003000200012Q0036000300013Q0020660003000300092Q001500056Q005300030005000200106900020008000300206600030002000A2Q003B0003000200012Q004F000200024Q00193Q00013Q00013Q000E3Q0003093Q0063686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403093Q00696E74657266616365030D3Q0048696465557365726E616D6573030C3Q007465616D53652Q74696E677303053Q00656E656D7903043Q006E616D6503083Q00667269656E646C7903133Q00446973706C617944697374616E63655479706503043Q00456E756D031B3Q0048756D616E6F6964446973706C617944697374616E63655479706503043Q004E6F6E6503073Q005375626A65637400224Q00367Q00206B5Q00010020665Q000200120B000200034Q00533Q000200020006103Q002100013Q00044B3Q002100012Q003600015Q00206B00010001000400206B0001000100050006100001001D00013Q00044B3Q001D00012Q0036000100013Q00206B00010001000600206B00010001000700206B00010001000800065C000100180001000100044B3Q001800012Q0036000100013Q00206B00010001000600206B00010001000900206B0001000100080006100001001D00013Q00044B3Q001D000100126D0001000B3Q00206B00010001000C00206B00010001000D0010693Q000A000100044B3Q0021000100126D0001000B3Q00206B00010001000C00206B00010001000E0010693Q000A00012Q00193Q00017Q00283Q0003093Q00636861724361636865030A3Q006368696C64436F756E74028Q002Q033Q0062696E03083Q0064726177696E677303053Q00626F78336403063Q0063726561746503043Q004C696E6503093Q00546869636B6E652Q73026Q00F03F03073Q0056697369626C65010003073Q0076697369626C65030D3Q007472616365724F75746C696E65026Q00084003063Q0074726163657203073Q00626F7846692Q6C03063Q0053717561726503063Q0046692Q6C65642Q01030A3Q00626F784F75746C696E652Q033Q00626F7803103Q006865616C74684261724F75746C696E6503093Q006865616C7468426172030A3Q006865616C74685465787403043Q005465787403063Q0043656E74657203043Q006E616D6503063Q00706C6179657203043Q004E616D6503093Q0063686172616374657203083Q0064697374616E636503063Q00776561706F6E03063Q0068692Q64656E030C3Q00612Q726F774F75746C696E6503083Q00547269616E676C6503053Q00612Q726F7703103Q0072656E646572436F2Q6E656374696F6E03093Q0048656172746265617403073Q00436F2Q6E65637401CB4Q000300015Q0010693Q0001000100304Q000200032Q000300015Q0010693Q000400012Q000300013Q00032Q0003000200044Q0003000300023Q00206600043Q000700120B000600084Q000300073Q000200302Q00070009000A00302Q0007000B000C2Q005300040007000200206600053Q000700120B000700084Q000300083Q000200302Q00080009000A00302Q0008000B000C2Q005300050008000200206600063Q000700120B000800084Q000300093Q000200302Q00090009000A00302Q0009000B000C2Q0013000600094Q000100033Q00012Q0003000400023Q00206600053Q000700120B000700084Q000300083Q000200302Q00080009000A00302Q0008000B000C2Q005300050008000200206600063Q000700120B000800084Q000300093Q000200302Q00090009000A00302Q0009000B000C2Q005300060009000200206600073Q000700120B000900084Q0003000A3Q000200302Q000A0009000A00302Q000A000B000C2Q00130007000A4Q000100043Q00012Q0003000500023Q00206600063Q000700120B000800084Q000300093Q000200302Q00090009000A00302Q0009000B000C2Q005300060009000200206600073Q000700120B000900084Q0003000A3Q000200302Q000A0009000A00302Q000A000B000C2Q00530007000A000200206600083Q000700120B000A00084Q0003000B3Q000200302Q000B0009000A00302Q000B000B000C2Q00130008000B4Q000100053Q00012Q0003000600023Q00206600073Q000700120B000900084Q0003000A3Q000200302Q000A0009000A00302Q000A000B000C2Q00530007000A000200206600083Q000700120B000A00084Q0003000B3Q000200302Q000B0009000A00302Q000B000B000C2Q00530008000B000200206600093Q000700120B000B00084Q0003000C3Q000200302Q000C0009000A00302Q000C000B000C2Q00130009000C4Q000100063Q00012Q00630002000400010010690001000600022Q000300023Q000B00206600033Q000700120B000500084Q000300063Q000200302Q00060009000F00302Q0006000B000C2Q00530003000600020010690002000E000300206600033Q000700120B000500084Q000300063Q000200302Q00060009000A00302Q0006000B000C2Q005300030006000200106900020010000300206600033Q000700120B000500124Q000300063Q000200302Q00060013001400302Q0006000B000C2Q005300030006000200106900020011000300206600033Q000700120B000500124Q000300063Q000200302Q00060009000F00302Q0006000B000C2Q005300030006000200106900020015000300206600033Q000700120B000500124Q000300063Q000200302Q00060009000A00302Q0006000B000C2Q005300030006000200106900020016000300206600033Q000700120B000500084Q000300063Q000200302Q00060009000F00302Q0006000B000C2Q005300030006000200106900020017000300206600033Q000700120B000500084Q000300063Q000200302Q00060009000A00302Q0006000B000C2Q005300030006000200106900020018000300206600033Q000700120B0005001A4Q000300063Q000200302Q0006001B001400302Q0006000B000C2Q005300030006000200106900020019000300206600033Q000700120B0005001A4Q000300063Q000300206B00073Q001D0006100007009C00013Q00044B3Q009C000100206B00073Q001D00206B00070007001E00065C0007009E0001000100044B3Q009E000100206B00073Q001F00206B00070007001E0010690006001A000700302Q0006001B001400302Q0006000B000C2Q00530003000600020010690002001C000300206600033Q000700120B0005001A4Q000300063Q000200302Q0006001B001400302Q0006000B000C2Q005300030006000200106900020020000300206600033Q000700120B0005001A4Q000300063Q000200302Q0006001B001400302Q0006000B000C2Q00530003000600020010690002002100030010690001000D00022Q000300023Q000200206600033Q000700120B000500244Q000300063Q000200302Q00060009000F00302Q0006000B000C2Q005300030006000200106900020023000300206600033Q000700120B000500244Q000300063Q000200302Q00060013001400302Q0006000B000C2Q00530003000600020010690002002500030010690001002200020010693Q000500012Q003600015Q00206B00010001002700206600010001002800065500033Q000100012Q001A8Q00530001000300020010693Q002600012Q00193Q00013Q00013Q00023Q0003063Q0055706461746503063Q0052656E64657201094Q003600015Q0020660001000100012Q001500036Q002D0001000300012Q003600015Q0020660001000100022Q001500036Q002D0001000300012Q00193Q00017Q00053Q0003073Q0044726177696E672Q033Q006E657703043Q006E6578742Q033Q0062696E026Q00F03F03123Q00126D000300013Q00206B0003000300022Q0015000400014Q001400030002000200126D000400034Q0015000500024Q005B000600063Q00044B3Q000900012Q0059000300070008000616000400080001000200044B3Q0008000100206B00043Q000400206B00053Q00042Q0075000500053Q0020180005000500052Q00590004000500032Q004F000300024Q00193Q00017Q00053Q0003103Q0072656E646572436F2Q6E656374696F6E030A3Q00446973636F2Q6E65637403043Q006E6578742Q033Q0062696E03063Q0052656D6F7665010F3Q00206B00013Q00010020660001000100022Q003B00010002000100126D000100033Q00206B00023Q00042Q005B000300033Q00044B3Q000900010020660006000500052Q003B000600020001000616000100070001000200044B3Q000700012Q003600016Q001500026Q003B0001000200012Q00193Q00017Q002E3Q0003093Q00696E7465726661636503093Q0063686172616374657203063Q00506172656E7403063Q006865616C746803093Q006D61784865616C746803093Q006765744865616C7468028Q0003073Q00656E61626C6564010003083Q006F6E5363722Q656E03063Q00706C6179657203163Q00476574506C6179657246726F6D43686172616374657203083Q0064726177696E677303073Q0076697369626C6503043Q006E616D6503043Q005465787403043Q004E616D6503093Q0077686974656C69737403063Q00557365724964030A3Q006973467269656E646C7903073Q006F7074696F6E73030C3Q007465616D53652Q74696E677303083Q00667269656E646C7903053Q00656E656D7903063Q00776561706F6E03093Q00676574576561706F6E03043Q004865616403083Q00506F736974696F6E03083Q0064697374616E6365030E3Q0073686172656453652Q74696E6773030D3Q006C696D697444697374616E6365030B3Q006D617844697374616E636503093Q00636861724361636865026Q00F03F03083Q00426173655061727403053Q00546F72736F030A3Q00552Q706572546F72736F03073Q00636F726E657273030E3Q006F2Q665363722Q656E412Q726F7703063Q00434672616D6503063Q00416E676C657303013Q005A03013Q005803093Q00646972656374696F6E03073Q00566563746F72322Q033Q006E657701D13Q00206B00013Q000100206B00023Q00020006100002000700013Q00044B3Q0007000100206B00030002000300065C000300080001000100044B3Q000800012Q00193Q00013Q00206B0003000100062Q0015000400024Q00230003000200040010693Q000500040010693Q0004000300206B00033Q0004002662000300130001000700044B3Q0013000100304Q0008000900304Q000A00092Q00193Q00013Q00206B00033Q000B00065C000300240001000100044B3Q002400012Q003600035Q00206600030003000C2Q0015000500024Q00530003000500020010693Q000B000300206B00033Q000B0006100003002400013Q00044B3Q0024000100206B00033Q000D00206B00030003000E00206B00030003000F00206B00043Q000B00206B0004000400110010690003001000042Q000600035Q00206B00043Q000B0006100004003A00013Q00044B3Q003A000100206B0004000100122Q0075000400043Q000E270007003A0001000400044B3Q003A00012Q0036000400013Q00206B00050001001200206B00063Q000B2Q005300040006000200065C000400390001000100044B3Q003900012Q0036000400013Q00206B00050001001200206B00063Q000B00206B0006000600132Q00530004000600020006100004003A00013Q00044B3Q003A00012Q0006000300013Q00206B0004000100142Q0015000500024Q001400040002000200065C000400400001000100044B3Q004000012Q0015000400033Q00206B0005000100160006100004004600013Q00044B3Q0046000100120B000600173Q00065C000600470001000100044B3Q0047000100120B000600184Q00070005000500060010693Q0015000500206B00050001001A2Q0015000600024Q00140005000200020010693Q0019000500206B00053Q0015000672000600510001000500044B3Q0051000100206B0006000500080010693Q0008000600206B00063Q00080006100006005900013Q00044B3Q005900012Q0036000600024Q0015000700023Q00120B0008001B4Q005300060008000200065C0006005C0001000100044B3Q005C00012Q00193Q00014Q0036000700033Q00206B00080006001C2Q00230007000200090010693Q000A00080010693Q001D000900206B000A0001001E00206B000A000A001F000610000A006A00013Q00044B3Q006A000100206B000A0001001E00206B000A000A002000066C000A006A0001000900044B3Q006A000100304Q000A000900206B000A3Q000A000610000A00AB00013Q00044B3Q00AB000100206B000A3Q00212Q0036000B00044Q0015000C00024Q0014000B000200022Q0036000C00054Q0015000D000A4Q003B000C0002000100120B000C00224Q0075000D000B3Q00120B000E00223Q000409000C008E00012Q00070010000B000F2Q0036001100064Q0015001200103Q00120B001300234Q00530011001300020006100011008D00013Q00044B3Q008D00012Q0036001100073Q00206B0012001000112Q00140011000200020006100011008D00013Q00044B3Q008D00012Q0036001100083Q00206B00120002001100206B0013001000112Q005300110013000200065C0011008D0001000100044B3Q008D00012Q00750011000A3Q0020180011001100222Q0059000A00110010000478000C007800012Q0075000C000A3Q00261F000C00A40001000700044B3Q00A400012Q0036000C00024Q0015000D00023Q00120B000E00244Q0053000C000E000200065C000C00A10001000100044B3Q00A100012Q0036000C00024Q0015000D00023Q00120B000E00254Q0053000C000E000200065C000C00A10001000100044B3Q00A100012Q0036000C00024Q0015000D00023Q00120B000E001B4Q0053000C000E0002000610000C00A400013Q00044B3Q00A40001001069000A0022000C2Q0036000C00094Q0036000D000A4Q0015000E000A4Q0057000D000E4Q001C000C3Q00020010693Q0026000C00044B3Q00D00001000610000500D000013Q00044B3Q00D0000100206B000A00050027000610000A00D000013Q00044B3Q00D000012Q0036000A000B4Q0036000B000C3Q00206B000B000B00282Q0023000A0002000C00126D000D00283Q00206B000D000D002900120B000E00074Q0015000F000B4Q00150010000C4Q0053000D001000022Q0036000E000C3Q00206B000E000E002800206B000E000E001C2Q0026000D000D000E2Q0036000E000D4Q0015000F000D3Q00206B00100006001C2Q0053000E001000022Q0036000F000E3Q00206B0010000E002A00206B0011000E002B2Q0053000F0011000200126D0010002D3Q00206B00100010002E2Q00360011000F4Q00150012000F4Q00140011000200022Q0036001200104Q00150013000F4Q0057001200134Q001C00103Q00020010693Q002C00102Q00193Q00017Q005B3Q0003083Q006F6E5363722Q656E03073Q00656E61626C656403083Q0064726177696E677303073Q0076697369626C6503063Q0068692Q64656E03053Q00626F78336403093Q00696E7465726661636503073Q006F7074696F6E7303073Q00636F726E6572732Q033Q00626F7803073Q0056697369626C65030A3Q00626F784F75746C696E6503083Q00506F736974696F6E03073Q00746F704C65667403043Q0053697A65030B3Q00626F2Q746F6D526967687403053Q00436F6C6F7203083Q00626F78436F6C6F72026Q00F03F030C3Q005472616E73706172656E6379027Q0040030F3Q00626F784F75746C696E65436F6C6F7203073Q00626F7846692Q6C030C3Q00626F7846692Q6C436F6C6F7203093Q006865616C746842617203103Q006865616C74684261724F75746C696E65030A3Q00626F2Q746F6D4C65667403023Q00546F03043Q0046726F6D03063Q006865616C746803093Q006D61784865616C7468030A3Q006479696E67436F6C6F72030C3Q006865616C746879436F6C6F7203153Q006865616C74684261724F75746C696E65436F6C6F72030A3Q006865616C74685465787403043Q005465787403023Q006870030E3Q0073686172656453652Q74696E677303083Q007465787453697A6503043Q00466F6E7403083Q0074657874466F6E74030F3Q006865616C746854657874436F6C6F7203073Q004F75746C696E6503113Q006865616C7468546578744F75746C696E65030C3Q004F75746C696E65436F6C6F7203163Q006865616C7468546578744F75746C696E65436F6C6F72030A3Q0054657874426F756E6473026Q00E03F03043Q006E616D6503093Q006E616D65436F6C6F72030B3Q006E616D654F75746C696E6503103Q006E616D654F75746C696E65436F6C6F7203083Q00746F70526967687403073Q00566563746F723203053Q00794178697303013Q005903083Q0064697374616E636503063Q00207374756473030D3Q0064697374616E6365436F6C6F72030F3Q0064697374616E63654F75746C696E6503143Q0064697374616E63654F75746C696E65436F6C6F7203063Q00776561706F6E030B3Q00776561706F6E436F6C6F72030D3Q00776561706F6E4F75746C696E6503123Q00776561706F6E4F75746C696E65436F6C6F7203043Q007A65726F03063Q00747261636572030D3Q007472616365724F75746C696E65030B3Q00747261636572436F6C6F72030C3Q007472616365724F726967696E03063Q004D692Q646C652Q033Q00546F702Q033Q006E6577028Q0003063Q00426F2Q746F6D03123Q007472616365724F75746C696E65436F6C6F7203053Q00612Q726F77030E3Q006F2Q665363722Q656E412Q726F7703093Q00646972656374696F6E00030C3Q00612Q726F774F75746C696E6503153Q006F2Q665363722Q656E412Q726F774F75746C696E6503053Q007063612Q6C03063Q00506F696E744203063Q00506F696E744102CD5QCCDC3F03123Q006F2Q665363722Q656E412Q726F7753697A6503063Q00506F696E744302CD5QCCDCBF03133Q006F2Q665363722Q656E412Q726F77436F6C6F72031A3Q006F2Q665363722Q656E412Q726F774F75746C696E65436F6C6F7201E4012Q00206B00013Q000100065C000100040001000100044B3Q000400012Q000600015Q00206B00023Q000200065C000200080001000100044B3Q000800012Q000600025Q00206B00033Q000300206B00030003000400206B00043Q000300206B00040004000500206B00053Q000300206B00050005000600206B00063Q000700206B00073Q000800206B00083Q000900206B00090003000A000672000A00170001000200044B3Q00170001000672000A00170001000100044B3Q0017000100206B000A0007000A0010690009000B000A00206B00090003000C00206B000A0003000A00206B000A000A000B000610000A001E00013Q00044B3Q001E000100206B000A0007000C0010690009000B000A00206B00090003000A00206B00090009000B0006100009003B00013Q00044B3Q003B000100206B00090003000A00206B000A0008000E0010690009000D000A00206B000A0008001000206B000B0008000E2Q0077000A000A000B0010690009000F000A00206B000A0007001200206B000A000A001300106900090011000A00206B000A0007001200206B000A000A001500106900090014000A00206B000A0003000C00206B000B0009000D001069000A000D000B00206B000B0009000F001069000A000F000B00206B000B0007001600206B000B000B0013001069000A0011000B00206B000B0007001600206B000B000B0015001069000A0014000B00206B000900030017000672000A00410001000200044B3Q00410001000672000A00410001000100044B3Q0041000100206B000A000700170010690009000B000A00206B00090003001700206B00090009000B0006100009005300013Q00044B3Q0053000100206B00090003001700206B000A0008000E0010690009000D000A00206B000A0008001000206B000B0008000E2Q0077000A000A000B0010690009000F000A00206B000A0007001800206B000A000A001300106900090011000A00206B000A0007001800206B000A000A001500106900090014000A00206B000900030019000672000A00590001000200044B3Q00590001000672000A00590001000100044B3Q0059000100206B000A000700190010690009000B000A00206B00090003001A00206B000A0003001900206B000A000A000B000610000A006000013Q00044B3Q0060000100206B000A0007001A0010690009000B000A00206B00090003001900206B00090009000B0006100009008A00013Q00044B3Q008A000100206B00090008000E2Q0036000A6Q007700090009000A00206B000A0008001B2Q0036000B6Q0077000A000A000B00206B000B00030019001069000B001C000A2Q0036000C00014Q0015000D000A4Q0015000E00093Q00206B000F3Q001E00206B00103Q001F2Q005A000F000F00102Q0053000C000F0002001069000B001D000C2Q0036000C00023Q00206B000D0007002000206B000E0007002100206B000F3Q001E00206B00103Q001F2Q005A000F000F00102Q0053000C000F0002001069000B0011000C00206B000C0003001A2Q0036000D00034Q0026000D000A000D001069000C001C000D2Q0036000D00034Q0077000D0009000D001069000C001D000D00206B000D0007002200206B000D000D0013001069000C0011000D00206B000D0007002200206B000D000D0015001069000C0014000D00206B000900030023000672000A00900001000200044B3Q00900001000672000A00900001000100044B3Q0090000100206B000A000700230010690009000B000A00206B00090003002300206B00090009000B000610000900BF00013Q00044B3Q00BF000100206B00090008000E2Q0036000A6Q007700090009000A00206B000A0008001B2Q0036000B6Q0077000A000A000B00206B000B000300232Q0036000C00043Q00206B000D3Q001E2Q0014000C0002000200120B000D00254Q0048000C000C000D001069000B0024000C00206B000C0006002600206B000C000C0027001069000B000F000C00206B000C0006002600206B000C000C0029001069000B0028000C00206B000C0007002A00206B000C000C0013001069000B0011000C00206B000C0007002A00206B000C000C0015001069000B0014000C00206B000C0007002C001069000B002B000C00206B000C0007002E001069000B002D000C2Q0036000C00014Q0015000D000A4Q0015000E00093Q00206B000F3Q001E00206B00103Q001F2Q005A000F000F00102Q0053000C000F000200206B000D000B002F002040000D000D00302Q0077000C000C000D2Q0036000D00054Q0077000C000C000D001069000B000D000C00206B000900030031000672000A00C50001000200044B3Q00C50001000672000A00C50001000100044B3Q00C5000100206B000A000700310010690009000B000A00206B00090003003100206B00090009000B000610000900E800013Q00044B3Q00E8000100206B00090003003100206B000A0006002600206B000A000A00270010690009000F000A00206B000A0006002600206B000A000A002900106900090028000A00206B000A0007003200206B000A000A001300106900090011000A00206B000A0007003200206B000A000A001500106900090014000A00206B000A000700330010690009002B000A00206B000A000700340010690009002D000A00206B000A0008000E00206B000B000800352Q0026000A000A000B002040000A000A003000126D000B00363Q00206B000B000B003700206B000C0009002F00206B000C000C00382Q000F000B000B000C2Q0077000A000A000B2Q0036000B00064Q0077000A000A000B0010690009000D000A00206B000900030039000672000A00F10001000200044B3Q00F10001000672000A00F10001000100044B3Q00F1000100206B000A3Q0039000610000A00F100013Q00044B3Q00F1000100206B000A000700390010690009000B000A00206B00090003003900206B00090009000B000610000900142Q013Q00044B3Q00142Q0100206B0009000300392Q0036000A00043Q00206B000B3Q00392Q0014000A0002000200120B000B003A4Q0048000A000A000B00106900090024000A00206B000A0006002600206B000A000A00270010690009000F000A00206B000A0006002600206B000A000A002900106900090028000A00206B000A0007003B00206B000A000A001300106900090011000A00206B000A0007003B00206B000A000A001500106900090014000A00206B000A0007003C0010690009002B000A00206B000A0007003D0010690009002D000A00206B000A0008001B00206B000B000800102Q0026000A000A000B002040000A000A00302Q0036000B00074Q0026000A000A000B0010690009000D000A00206B00090003003E000672000A001A2Q01000200044B3Q001A2Q01000672000A001A2Q01000100044B3Q001A2Q0100206B000A0007003E0010690009000B000A00206B00090003003E00206B00090009000B000610000900482Q013Q00044B3Q00482Q0100206B00090003003E00206B000A3Q003E00106900090024000A00206B000A0006002600206B000A000A00270010690009000F000A00206B000A0006002600206B000A000A002900106900090028000A00206B000A0007003F00206B000A000A001300106900090011000A00206B000A0007003F00206B000A000A001500106900090014000A00206B000A000700400010690009002B000A00206B000A000700410010690009002D000A00206B000A0008001B00206B000B000800102Q0026000A000A000B002040000A000A003000206B000B0003003900206B000B000B000B000610000B00442Q013Q00044B3Q00442Q012Q0036000B00073Q00126D000C00363Q00206B000C000C003700206B000D0003003900206B000D000D002F00206B000D000D00382Q000F000C000C000D2Q0026000B000B000C00065C000B00462Q01000100044B3Q00462Q0100126D000B00363Q00206B000B000B00422Q0026000A000A000B0010690009000D000A00206B000900030043000672000A004E2Q01000200044B3Q004E2Q01000672000A004E2Q01000100044B3Q004E2Q0100206B000A000700430010690009000B000A00206B00090003004400206B000A0003004300206B000A000A000B000610000A00552Q013Q00044B3Q00552Q0100206B000A000700440010690009000B000A00206B00090003004300206B00090009000B000610000900922Q013Q00044B3Q00922Q0100206B00090003004300206B000A0007004500206B000A000A001300106900090011000A00206B000A0007004500206B000A000A001500106900090014000A00206B000A0008001B00206B000B000800102Q0026000A000A000B002040000A000A00300010690009001C000A00206B000A0007004600261F000A006D2Q01004700044B3Q006D2Q012Q0036000A00083Q002040000A000A003000065C000A00862Q01000100044B3Q00862Q0100206B000A0007004600261F000A00792Q01004800044B3Q00792Q012Q0036000A00083Q00126D000B00363Q00206B000B000B004900120B000C00303Q00120B000D004A4Q0053000B000D00022Q000F000A000A000B00065C000A00862Q01000100044B3Q00862Q0100206B000A0007004600261F000A00842Q01004B00044B3Q00842Q012Q0036000A00083Q00126D000B00363Q00206B000B000B004900120B000C00303Q00120B000D00134Q0053000B000D00022Q000F000A000A000B00044B3Q00862Q012Q002F000A6Q0006000A00013Q0010690009001D000A00206B000A0003004400206B000B0007004C00206B000B000B0013001069000A0011000B00206B000B0007004C00206B000B000B0015001069000A0014000B00206B000B0009001C001069000A001C000B00206B000B0009001D001069000A001D000B00206B00090004004D000672000A009F2Q01000200044B3Q009F2Q0100065C0001009D2Q01000100044B3Q009D2Q0100206B000A0007004E000610000A009F2Q013Q00044B3Q009F2Q0100206B000A3Q004F00261F000A009E2Q01005000044B3Q009E2Q012Q002F000A6Q0006000A00013Q0010690009000B000A00206B00090004005100206B000A0004004D00206B000A000A000B000610000A00A62Q013Q00044B3Q00A62Q0100206B000A000700520010690009000B000A00206B00090004004D00206B00090009000B000610000900DB2Q013Q00044B3Q00DB2Q0100206B00090004004D00126D000A00533Q000655000B3Q000100062Q001A3Q00094Q00123Q00094Q00123Q000A4Q00123Q00084Q001A8Q001A3Q00074Q003B000A0002000100206B000A000900552Q0036000B000B3Q00206B000C3Q004F00120B000D00564Q0053000B000D000200206B000C000700572Q000F000B000B000C2Q0077000A000A000B00106900090054000A00206B000A000900552Q0036000B000B3Q00206B000C3Q004F00120B000D00594Q0053000B000D000200206B000C000700572Q000F000B000B000C2Q0077000A000A000B00106900090058000A00206B000A0007005A00206B000A000A001300106900090011000A00206B000A0007005A00206B000A000A001500106900090014000A00206B000A0004005100206B000B00090055001069000A0055000B00206B000B00090054001069000A0054000B00206B000B00090058001069000A0058000B00206B000B0007005B00206B000B000B0013001069000A0011000B00206B000B0007005B00206B000B000B0015001069000A0014000B2Q005100095Q00126D000900533Q000655000A0001000100052Q001A3Q00024Q001A3Q00014Q001A3Q00074Q001A3Q00054Q001A3Q00084Q003B0009000200012Q00193Q00013Q00023Q00073Q0003063Q00506F696E7441026Q00E03F03093Q00646972656374696F6E03143Q006F2Q665363722Q656E412Q726F7752616469757303073Q00566563746F72322Q033Q006F6E65026Q00394000174Q003600016Q0036000200014Q0036000300024Q0036000400033Q0020400004000400022Q0036000500043Q00206B0005000500032Q0036000600053Q00206B0006000600042Q000F0005000500062Q002600040004000500126D000500053Q00206B0005000500060020400005000500072Q00530003000500022Q0036000400033Q00126D000500053Q00206B0005000500060020400005000500072Q00770004000400052Q00530002000400020010690001000100022Q00193Q00017Q000E3Q0003053Q00626F783364026Q00F03F03073Q0056697369626C6503053Q00436F6C6F72030A3Q00626F783364436F6C6F72030C3Q005472616E73706172656E6379027Q004003043Q0046726F6D03073Q00636F726E65727303023Q00546F026Q001040026Q001440026Q000840026Q002040005B4Q003600015Q0006100001000800013Q00044B3Q000800012Q0036000100013Q0006100001000800013Q00044B3Q000800012Q0036000100023Q00206B00010001000100120B000200024Q0036000300034Q0075000300033Q00120B000400023Q0004090002005A00012Q0036000600034Q000700060006000500120B000700024Q0075000800063Q00120B000900023Q0004090007001E00012Q0007000B0006000A001069000B000300012Q0036000C00023Q00206B000C000C000500206B000C000C0002001069000B0004000C2Q0036000C00023Q00206B000C000C000500206B000C000C0007001069000B0006000C0004780007001300010006100001005900013Q00044B3Q0059000100206B0007000600022Q0036000800043Q00206B0008000800092Q00070008000800050010690007000800082Q0036000800043Q00206B00080008000900261F0005002C0001000B00044B3Q002C000100120B000900023Q00065C0009002D0001000100044B3Q002D00010020180009000500022Q00070008000800090010690007000A000800206B0008000600072Q0036000900043Q00206B00090009000900261F000500370001000B00044B3Q0037000100120B000A00023Q00065C000A00380001000100044B3Q00380001002018000A000500022Q000700090009000A0010690008000800092Q0036000900043Q00206B00090009000900261F000500410001000B00044B3Q0041000100120B000A000C3Q00065C000A00420001000100044B3Q00420001002018000A0005000C2Q000700090009000A0010690008000A000900206B00090006000D2Q0036000A00043Q00206B000A000A000900261F0005004C0001000B00044B3Q004C000100120B000B000C3Q00065C000B004D0001000100044B3Q004D0001002018000B0005000C2Q0007000A000A000B00106900090008000A2Q0036000A00043Q00206B000A000A000900261F000500560001000B00044B3Q0056000100120B000B000E3Q00065C000B00570001000100044B3Q00570001002018000B0005000B2Q0007000A000A000B0010690009000A000A0004780002000D00012Q00193Q00017Q00073Q00030C3Q007365746D6574617461626C6503093Q0063686172616374657203063Q00612Q73657274032E3Q004D692Q73696E6720617267756D656E7420233120284D6F64656C2F4368617261637465722065787065637465642903093Q00696E7465726661636503243Q004D692Q73696E6720617267756D656E7420233220287461626C652065787065637465642903093Q00436F6E73747275637402123Q00126D000200014Q000300036Q003600046Q005300020004000200126D000300034Q001500045Q00120B000500044Q005300030005000200106900020002000300126D000300034Q0015000400013Q00120B000500064Q00530003000500020010690002000500030020660003000200072Q003B0003000200012Q004F000200024Q00193Q00017Q00073Q0003093Q00686967686C6967687403083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403103Q00757064617465436F2Q6E656374696F6E03093Q0048656172746265617403073Q00436F2Q6E656374010E3Q00126D000100023Q00206B00010001000300120B000200044Q003600036Q00530001000300020010693Q000100012Q0036000100013Q00206B00010001000600206600010001000700065500033Q000100012Q001A8Q00530001000300020010693Q000500012Q00193Q00013Q00013Q00013Q0003063Q0055706461746500044Q00367Q0020665Q00012Q003B3Q000200012Q00193Q00017Q00043Q0003103Q00757064617465436F2Q6E656374696F6E030A3Q00446973636F2Q6E65637403093Q00686967686C6967687403073Q0044657374726F79010A3Q00206B00013Q00010020660001000100022Q003B00010002000100206B00013Q00030020660001000100042Q003B0001000200012Q003600016Q001500026Q003B0001000200012Q00193Q00017Q00203Q0003093Q0063686172616374657203063Q00506172656E7403093Q00686967686C6967687403093Q00696E7465726661636503093Q006765744865616C7468028Q0003073Q00456E61626C6564010003163Q00476574506C6179657246726F6D43686172616374657203093Q0077686974656C69737403063Q00557365724964030A3Q006973467269656E646C79030C3Q007465616D53652Q74696E677303083Q00667269656E646C7903053Q00656E656D7903073Q00656E61626C656403053Q006368616D7303093Q0044657074684D6F646503103Q006368616D7356697369626C654F6E6C7903043Q00456E756D03123Q00486967686C6967687444657074684D6F646503083Q004F2Q636C75646564030B3Q00416C776179734F6E546F7003073Q0041646F726E2Q6503093Q0046692Q6C436F6C6F72030E3Q006368616D7346692Q6C436F6C6F72026Q00F03F03103Q0046692Q6C5472616E73706172656E6379027Q0040030C3Q004F75746C696E65436F6C6F7203113Q006368616D734F75746C696E65436F6C6F7203133Q004F75746C696E655472616E73706172656E637901583Q00206B00013Q00010006100001000600013Q00044B3Q0006000100206B00020001000200065C000200070001000100044B3Q000700012Q00193Q00013Q00206B00023Q000300206B00033Q000400206B0004000300052Q0015000500014Q0014000400020002002662000400100001000600044B3Q0010000100302Q0002000700082Q00193Q00014Q003600055Q0020660005000500092Q0015000700014Q00530005000700022Q000600065Q0006100005002800013Q00044B3Q0028000100206B00070003000A2Q0075000700073Q000E27000600280001000700044B3Q002800012Q0036000700013Q00206B00080003000A2Q0015000900054Q005300070009000200065C000700270001000100044B3Q002700012Q0036000700013Q00206B00080003000A00206B00090005000B2Q00530007000900020006100007002800013Q00044B3Q002800012Q0006000600013Q00206B00070003000C2Q0015000800014Q001400070002000200065C0007002E0001000100044B3Q002E00012Q0015000700063Q00206B00080003000D0006100007003400013Q00044B3Q0034000100120B0009000E3Q00065C000900350001000100044B3Q0035000100120B0009000F4Q000700080008000900206B000900080010000672000A003A0001000900044B3Q003A000100206B000A0008001100106900020007000A00206B000A00020007000610000A005700013Q00044B3Q0057000100206B000A00080013000610000A004600013Q00044B3Q0046000100126D000A00143Q00206B000A000A001500206B000A000A001600065C000A00490001000100044B3Q0049000100126D000A00143Q00206B000A000A001500206B000A000A001700106900020012000A00106900020018000100206B000A0008001A00206B000A000A001B00106900020019000A00206B000A0008001A00206B000A000A001D0010690002001C000A00206B000A0008001F00206B000A000A001B0010690002001E000A00206B000A0008001F00206B000A000A001D00106900020020000A2Q00193Q00017Q00073Q00030C3Q007365746D6574617461626C6503083Q00696E7374616E636503063Q00612Q7365727403273Q004D692Q73696E6720617267756D656E742023312028496E7374616E63652045787065637465642903073Q006F7074696F6E7303243Q004D692Q73696E6720617267756D656E7420233220287461626C652065787065637465642903093Q00436F6E73747275637402123Q00126D000200014Q000300036Q003600046Q005300020004000200126D000300034Q001500045Q00120B000500044Q005300030005000200106900020002000300126D000300034Q0015000400013Q00120B000500064Q00530003000500020010690002000500030020660003000200072Q003B0003000200012Q004F000200024Q00193Q00017Q00193Q0003073Q006F7074696F6E7303073Q00656E61626C65640003043Q007465787403063Q007B6E616D657D03093Q0074657874436F6C6F7203063Q00436F6C6F72332Q033Q006E6577026Q00F03F030B3Q00746578744F75746C696E6503103Q00746578744F75746C696E65436F6C6F7203083Q007465787453697A65026Q002A4003083Q0074657874466F6E74027Q0040030D3Q006C696D697444697374616E6365030B3Q006D617844697374616E6365025Q00C0624003073Q0044726177696E6703043Q005465787403063Q0043656E7465722Q0103103Q0072656E646572436F2Q6E656374696F6E03093Q0048656172746265617403073Q00436F2Q6E656374014D3Q00206B00013Q000100206B00020001000200261F000200070001000300044B3Q000700012Q0006000200013Q00065C000200080001000100044B3Q0008000100206B00020001000200106900010002000200206B00020001000400065C0002000D0001000100044B3Q000D000100120B000200053Q00106900010004000200206B00020001000600065C0002001A0001000100044B3Q001A00012Q0003000200023Q00126D000300073Q00206B00030003000800120B000400093Q00120B000500093Q00120B000600094Q005300030006000200120B000400094Q006300020002000100106900010006000200206B00020001000A00261F000200210001000300044B3Q002100012Q0006000200013Q00065C000200220001000100044B3Q0022000100206B00020001000A0010690001000A000200206B00020001000B00065C000200290001000100044B3Q0029000100126D000200073Q00206B0002000200082Q003D0002000100020010690001000B000200206B00020001000C00065C0002002E0001000100044B3Q002E000100120B0002000D3Q0010690001000C000200206B00020001000E00065C000200330001000100044B3Q0033000100120B0002000F3Q0010690001000E000200206B00020001001000065C000200380001000100044B3Q003800012Q000600025Q00106900010010000200206B00020001001100065C0002003D0001000100044B3Q003D000100120B000200123Q00106900010011000200126D000200133Q00206B00020002000800120B000300144Q00140002000200020010693Q0004000200206B00023Q000400302Q0002001500162Q003600025Q00206B00020002001800206600020002001900065500043Q000100012Q001A8Q00530002000400020010693Q001700022Q00193Q00013Q00013Q00013Q0003063Q0052656E64657201054Q003600015Q0020660001000100012Q001500036Q002D0001000300012Q00193Q00017Q00043Q0003103Q0072656E646572436F2Q6E656374696F6E030A3Q00446973636F2Q6E65637403043Q007465787403063Q0052656D6F766501073Q00206B00013Q00010020660001000100022Q003B00010002000100206B00013Q00030020660001000100042Q003B0001000200012Q00193Q00017Q00213Q0003083Q00696E7374616E636503063Q00506172656E7403083Q00446573747275637403043Q007465787403073Q006F7074696F6E7303073Q00656E61626C656403073Q0056697369626C65010003083Q00506F736974696F6E030D3Q006C696D697444697374616E6365030B3Q006D617844697374616E636503053Q00436F6C6F7203093Q0074657874436F6C6F72026Q00F03F030C3Q005472616E73706172656E6379027Q004003073Q004F75746C696E65030B3Q00746578744F75746C696E65030C3Q004F75746C696E65436F6C6F7203103Q00746578744F75746C696E65436F6C6F7203043Q0053697A65030C3Q00457370496E74657266616365030E3Q0073686172656453652Q74696E677303083Q007465787453697A6503043Q00466F6E7403083Q0074657874466F6E7403043Q005465787403043Q006773756203063Q007B6E616D657D03043Q004E616D65030A3Q007B64697374616E63657D030A3Q007B706F736974696F6E7D03083Q00746F737472696E67014E3Q00206B00013Q00010006100001000600013Q00044B3Q0006000100206B00020001000200065C000200090001000100044B3Q0009000100206600023Q00032Q0025000200034Q003100025Q00206B00023Q000400206B00033Q000500206B00040003000600065C000400100001000100044B3Q0010000100302Q0002000700082Q00193Q00014Q003600046Q0015000500014Q001400040002000200206B0004000400092Q0036000500014Q0015000600044Q002300050002000700206B00080003000A0006100008001E00013Q00044B3Q001E000100206B00080003000B00066C0008001E0001000700044B3Q001E00012Q000600065Q00106900020007000600206B0008000200070006100008004D00013Q00044B3Q004D000100106900020009000500206B00080003000D00206B00080008000E0010690002000C000800206B00080003000D00206B0008000800100010690002000F000800206B00080003001200106900020011000800206B00080003001400106900020013000800126D000800163Q00206B00080008001700206B00080008001800065C000800330001000100044B3Q0033000100206B00080003001800106900020015000800126D000800163Q00206B00080008001700206B00080008001A00065C0008003A0001000100044B3Q003A000100206B00080003001A00106900020019000800206B00080003000400206600080008001C00120B000A001D3Q00206B000B0001001E2Q00530008000B000200206600080008001C00120B000A001F4Q0036000B00024Q0015000C00074Q0057000B000C4Q001C00083Q000200206600080008001C00120B000A00203Q00126D000B00214Q0015000C00044Q0057000B000C4Q001C00083Q00020010690002001B00082Q00193Q00017Q00053Q00030C3Q005F6F626A656374436163686503043Q007761726E03203Q00496E7374616E63652068616E646C657220616C7265616479206578697374732E2Q033Q006E6577026Q00F03F02154Q003600025Q00206B0002000200012Q0007000300023Q0006100003000900013Q00044B3Q0009000100126D000300023Q00120B000400034Q003B00030002000100044B3Q001100012Q000300036Q0036000400013Q00206B0004000400042Q001500056Q0015000600014Q0013000400064Q000100033Q00012Q005900023Q00032Q0007000300023Q00206B0003000300052Q004F000300024Q00193Q00017Q000A3Q0003043Q006E657874030E3Q0073686172656453652Q74696E6773030C3Q007465616D53652Q74696E6773030C3Q005F6F626A6563744361636865026Q00F03F03083Q00696E7374616E636503073Q006F7074696F6E73030B3Q006D617844697374616E6365030D3Q006C696D697444697374616E636500024C3Q0006103Q000B00013Q00044B3Q000B000100126D000200014Q001500036Q005B000400043Q00044B3Q000900012Q003600075Q00206B0007000700022Q0059000700050006000616000200060001000200044B3Q000600010006100001002200013Q00044B3Q0022000100126D000200014Q0015000300014Q005B000400043Q00044B3Q002000012Q003600075Q00206B0007000700032Q00070007000700050006100007002000013Q00044B3Q0020000100126D000700014Q0015000800064Q005B000900093Q00044B3Q001E00012Q0036000C5Q00206B000C000C00032Q0007000C000C00052Q0059000C000A000B0006160007001A0001000200044B3Q001A0001000616000200110001000200044B3Q0011000100126D000200014Q003600035Q00206B0003000300042Q005B000400043Q00044B3Q0049000100120B000700054Q0075000800063Q00120B000900053Q0004090007004900012Q0007000B0006000A00206B000C000B0006000610000C004800013Q00044B3Q004800010006103Q004800013Q00044B3Q0048000100206B000C000B00072Q0036000D5Q00206B000D000D000200206B000D000D000800065C000D00390001000100044B3Q0039000100206B000D000B000700206B000D000D0008001069000C0008000D00206B000C000B00072Q0036000D5Q00206B000D000D000200206B000D000D000900265D000D00450001000A00044B3Q004500012Q0036000D5Q00206B000D000D000200206B000D000D000900065C000D00470001000100044B3Q0047000100206B000D000B000700206B000D000D0009001069000C0009000D0004780007002B0001000616000200270001000200044B3Q002700012Q00193Q00017Q000F3Q0003063Q00612Q73657274030A3Q005F6861734C6F61646564031C3Q004573702068617320616C726561647920622Q656E206C6F616465642E030C3Q005F636F2Q6E656374696F6E73030C3Q0052656D6F76654F626A656374030E3Q0046696E6446697273744368696C64030A3Q004368617261637465727303043Q006E657874030A3Q00476574506C6179657273030B3Q00506C61796572412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030E3Q00506C6179657252656D6F76696E672Q01004B3Q00126D3Q00014Q003600015Q00206B0001000100022Q003F000100013Q00120B000200034Q002D3Q000200012Q00368Q000300015Q0010693Q000400010006555Q000100052Q00123Q00014Q00123Q00024Q00128Q00123Q00034Q00123Q00044Q003600015Q00065500020001000100012Q00127Q00106900010005000200065500010002000100022Q001A8Q00127Q00065500020003000100022Q001A3Q00014Q00128Q0036000300053Q00206600030003000600120B000500074Q005300030005000200065C000300200001000100044B3Q002000012Q0036000300054Q0015000400024Q0015000500034Q003B00040002000100065500040004000100032Q00123Q00014Q001A8Q00127Q00126D000500084Q0036000600023Q0020660006000600092Q002300060002000700044B3Q002F00012Q0015000A00044Q0015000B00094Q003B000A000200010006160005002C0001000200044B3Q002C00012Q0036000500023Q00206B00050005000A00206600050005000B2Q0015000700044Q005300050007000200126D0006000C3Q00206B00060006000D2Q003600075Q00206B0007000700042Q0015000800054Q002D0006000800012Q0036000600023Q00206B00060006000E00206600060006000B00065500080005000100012Q00128Q005300060008000200126D0007000C3Q00206B00070007000D2Q003600085Q00206B0008000800042Q0015000900064Q002D0007000900012Q003600075Q00302Q00070002000F2Q00193Q00013Q00063Q00073Q0003093Q0043686172616374657203163Q00476574506C6179657246726F6D436861726163746572030E3Q0073686172656453652Q74696E6773030C3Q006E6F6E506C61796572455350030C3Q005F6F626A6563744361636865030C3Q0052656D6F76654F626A6563742Q033Q006E6577012C3Q0006103Q000600013Q00044B3Q000600012Q003600015Q00206B0001000100010006343Q00070001000100044B3Q000700012Q00193Q00014Q0036000100013Q0020660001000100022Q001500036Q005300010003000200065C000100130001000100044B3Q001300012Q0036000100023Q00206B00010001000300206B00010001000400065C000100130001000100044B3Q001300012Q00193Q00014Q0036000100023Q00206B0001000100052Q0007000100013Q0006100001001C00013Q00044B3Q001C00012Q0036000100023Q00206B0001000100062Q001500026Q003B0001000200012Q0036000100023Q00206B0001000100052Q0003000200014Q0036000300033Q00206B0003000300072Q001500046Q0036000500024Q00530003000500022Q0036000400043Q00206B0004000400072Q001500056Q0036000600024Q0013000400064Q000100023Q00012Q005900013Q00022Q00193Q00017Q00043Q00030C3Q005F6F626A6563744361636865026Q00F03F03083Q0044657374727563740001114Q003600015Q00206B0001000100012Q0007000100013Q0006100001001000013Q00044B3Q0010000100120B000200024Q0075000300013Q00120B000400023Q0004090002000D00012Q00070006000100050020660006000600032Q003B0006000200010004780002000900012Q003600025Q00206B00020002000100206F00023Q00042Q00193Q00017Q000B3Q002Q033Q0049734103053Q004D6F64656C03153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403043Q007461736B03053Q00737061776E030A3Q004368696C64412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030C3Q005F636F2Q6E656374696F6E7301213Q00206600013Q000100120B000300024Q005300010003000200065C000100060001000100044B3Q000600012Q00193Q00013Q00206600013Q000300120B000300044Q00530001000300020006100001001100013Q00044B3Q0011000100126D000100053Q00206B0001000100062Q003600026Q001500036Q002D0001000300012Q00193Q00014Q005B000100013Q00206B00023Q000700206600020002000800065500043Q000100032Q001A3Q00014Q00128Q001A8Q00530002000400022Q0015000100023Q00126D000200093Q00206B00020002000A2Q0036000300013Q00206B00030003000B2Q0015000400014Q002D0002000400012Q00193Q00013Q00013Q00053Q002Q033Q0049734103083Q0048756D616E6F6964030A3Q00446973636F2Q6E65637403043Q007461736B03053Q00737061776E010E3Q00206600013Q000100120B000300024Q00530001000300020006100001000D00013Q00044B3Q000D00012Q003600015Q0020660001000100032Q003B00010002000100126D000100043Q00206B0001000100052Q0036000200014Q0036000300024Q002D0001000300012Q00193Q00017Q00083Q0003043Q006E657874030E3Q0047657444657363656E64616E7473030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030C3Q005F636F2Q6E656374696F6E7303123Q0044657363656E64616E7452656D6F76696E67011F3Q00126D000100013Q00206600023Q00022Q002300020002000300044B3Q000700012Q003600066Q0015000700054Q003B000600020001000616000100040001000200044B3Q0004000100206B00013Q00030020660001000100042Q003600036Q005300010003000200126D000200053Q00206B0002000200062Q0036000300013Q00206B0003000300072Q0015000400014Q002D00020004000100206B00023Q000800206600020002000400065500043Q000100012Q00123Q00014Q005300020004000200126D000300053Q00206B0003000300062Q0036000400013Q00206B0004000400072Q0015000500024Q002D0003000500012Q00193Q00013Q00013Q00033Q002Q033Q0049734103053Q004D6F64656C030C3Q0052656D6F76654F626A656374010A3Q00206600013Q000100120B000300024Q00530001000300020006100001000900013Q00044B3Q000900012Q003600015Q00206B0001000100032Q001500026Q003B0001000200012Q00193Q00017Q000A3Q0003093Q0043686172616374657203043Q007461736B03053Q00737061776E030E3Q00436861726163746572412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030C3Q005F636F2Q6E656374696F6E7303113Q0043686172616374657252656D6F76696E67030C3Q0052656D6F76654F626A65637401224Q003600015Q0006343Q00040001000100044B3Q000400012Q00193Q00013Q00206B00013Q00010006100001000C00013Q00044B3Q000C000100126D000100023Q00206B0001000100032Q0036000200013Q00206B00033Q00012Q002D00010003000100206B00013Q00040020660001000100052Q0036000300014Q005300010003000200126D000200063Q00206B0002000200072Q0036000300023Q00206B0003000300082Q0015000400014Q002D00020004000100206B00023Q00090020660002000200052Q0036000400023Q00206B00040004000A2Q005300020004000200126D000300063Q00206B0003000300072Q0036000400023Q00206B0004000400082Q0015000500024Q002D0003000500012Q00193Q00017Q00023Q0003093Q00436861726163746572030C3Q0052656D6F76654F626A65637401083Q00206B00013Q00010006100001000700013Q00044B3Q000700012Q003600015Q00206B00010001000200206B00023Q00012Q003B0001000200012Q00193Q00017Q000A3Q0003063Q00612Q73657274030A3Q005F6861734C6F61646564031C3Q0045737020686173206E6F7420622Q656E206C6F61646564207965742E03043Q006E657874030C3Q005F6F626A6563744361636865026Q00F03F03083Q004465737472756374030C3Q005F636F2Q6E656374696F6E73030A3Q00446973636F2Q6E656374012Q00283Q00126D3Q00014Q003600015Q00206B00010001000200120B000200034Q002D3Q0002000100126D3Q00044Q003600015Q00206B0001000100052Q005B000200023Q00044B3Q0012000100120B000500064Q0075000600043Q00120B000700063Q0004090005001200012Q00070009000400080020660009000900072Q003B0009000200010004780005000E00010006163Q000A0001000200044B3Q000A00012Q00363Q00014Q003600015Q00206B0001000100052Q003B3Q0002000100126D3Q00044Q003600015Q00206B0001000100082Q005B000200023Q00044B3Q001F00010020660005000400092Q003B0005000200010006163Q001D0001000200044B3Q001D00012Q00363Q00014Q003600015Q00206B0001000100082Q003B3Q000200012Q00367Q00304Q0002000A2Q00193Q00017Q00043Q0003153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C03043Q004E616D65034Q00010B3Q00206600013Q000100120B000300024Q00530001000300020006100001000800013Q00044B3Q0008000100206B0002000100032Q004F000200023Q00044B3Q000A000100120B000200044Q004F000200024Q00193Q00017Q00023Q0003163Q00476574506C6179657246726F6D43686172616374657203043Q005465616D01183Q00065C3Q00040001000100044B3Q000400012Q000600016Q004F000100024Q003600015Q0020660001000100012Q001500036Q00530001000300020006100001001500013Q00044B3Q0015000100206B0002000100020006100002001400013Q00044B3Q0014000100206B0002000100022Q0036000300013Q00206B000300030002000620000200130001000300044B3Q001300012Q002F00026Q0006000200014Q004F000200024Q000600026Q004F000200024Q00193Q00017Q00043Q0003083Q0048756D616E6F696403063Q004865616C746803093Q004D61784865616C7468026Q005940010F3Q0006720001000600013Q00044B3Q000600012Q003600016Q001500025Q00120B000300014Q00530001000300020006100001000B00013Q00044B3Q000B000100206B00020001000200206B0003000100032Q0022000200033Q00120B000200043Q00120B000300044Q0022000200034Q00193Q00017Q00", GetFEnv(), ...);
