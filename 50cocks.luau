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
				if (Enum <= 28) then
					if (Enum <= 13) then
						if (Enum <= 6) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 1) then
									Stk[Inst[2]] = Inst[3];
								else
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 4) then
								if (Enum > 3) then
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
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum == 5) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 9) then
							if (Enum <= 7) then
								Stk[Inst[2]] = {};
							elseif (Enum > 8) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 11) then
							if (Enum > 10) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]]();
							end
						elseif (Enum > 12) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 20) then
						if (Enum <= 16) then
							if (Enum <= 14) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							elseif (Enum == 15) then
								do
									return Stk[Inst[2]];
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
						elseif (Enum <= 18) then
							if (Enum > 17) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum == 19) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 24) then
						if (Enum <= 22) then
							if (Enum > 21) then
								do
									return;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum > 23) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 26) then
						if (Enum > 25) then
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
								if (Mvm[1] == 53) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum == 27) then
						Stk[Inst[2]] = Env[Inst[3]];
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
				elseif (Enum <= 43) then
					if (Enum <= 35) then
						if (Enum <= 31) then
							if (Enum <= 29) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							elseif (Enum > 30) then
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
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 33) then
							if (Enum > 32) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum > 34) then
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
								if (Mvm[1] == 53) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 39) then
						if (Enum <= 37) then
							if (Enum == 36) then
								Stk[Inst[2]] = Inst[3] ~= 0;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 38) then
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
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 41) then
						if (Enum == 40) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum == 42) then
						Stk[Inst[2]]();
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 50) then
					if (Enum <= 46) then
						if (Enum <= 44) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						elseif (Enum == 45) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 48) then
						if (Enum > 47) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum == 49) then
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
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 54) then
					if (Enum <= 52) then
						if (Enum > 51) then
							Stk[Inst[2]] = {};
						else
							do
								return;
							end
						end
					elseif (Enum > 53) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 56) then
					if (Enum == 55) then
						VIP = Inst[3];
					else
						do
							return Stk[Inst[2]];
						end
					end
				elseif (Enum == 57) then
					if (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				else
					Stk[Inst[2]][Inst[3]] = Inst[4];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!0D3Q0003083Q004E6F5265636F696C030B3Q00436F2Q6E656374696F6E7303083Q0053652Q74696E677303073Q0047756E4D6F64732Q0103063Q00537072656164030C3Q00537072656164416D6F756E74028Q0003043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203063Q00746F2Q676C65003E4Q00348Q003400015Q0010083Q0001000100201900013Q00012Q003400025Q00100800010002000200201900013Q00012Q003400025Q00100800010003000200201900013Q00010020190001000100032Q003400025Q00100800010004000200201900013Q000100201900010001000300201900010001000400301700010001000500201900013Q000100201900010001000300201900010001000400301700010006000500201900013Q000100201900010001000300201900010001000400301700010007000800061A00013Q000100012Q00357Q00061A00020001000100012Q00357Q00061A00030002000100012Q00357Q00061A00040003000100032Q00358Q00353Q00014Q00353Q00023Q00061A00050004000100042Q00353Q00044Q00358Q00353Q00014Q00353Q00023Q00121B000600093Q00202D00060006000A00122E0008000B4Q000B00060008000200201900060006000C00061A00070005000100052Q00358Q00353Q00014Q00353Q00024Q00353Q00064Q00353Q00053Q00061A00080006000100022Q00358Q00353Q00034Q003400095Q00061A000A0007000100032Q00358Q00353Q00074Q00353Q00083Q0010080009000D000A2Q0038000900024Q00333Q00013Q00083Q00133Q0003083Q004E6F5265636F696C030B3Q00576561706F6E436163686503053Q00706169727303053Q00676574676303043Q007479706503053Q007461626C6503063Q0072617767657403093Q00457175697054696D6503063Q00696E73657274030E3Q004F726967696E616C56616C75657303063Q005265636F696C03163Q0043616D6572615265636F696C696E67456E61626C6564030A3Q00416E676C65585F4D696E030A3Q00416E676C65585F4D6178030A3Q00416E676C65595F4D696E030A3Q00416E676C65595F4D6178030A3Q00416E676C655A5F4D696E030A3Q00416E676C655A5F4D617803063Q00537072656164003C4Q00187Q0020195Q00012Q003400015Q0010083Q0002000100121B3Q00033Q00121B000100044Q001D000200014Q001C000100024Q000C5Q00020004253Q0039000100121B000500054Q0029000600044Q001200050002000200263900050039000100060004253Q0039000100121B000500074Q0029000600043Q00122E000700084Q000B0005000700020006360005003900013Q0004253Q0039000100121B000500063Q0020190005000500092Q001800065Q0020190006000600010020190006000600022Q0029000700044Q00140005000700012Q001800055Q00201900050005000100201900050005000A2Q001500050005000400062Q00050039000100010004253Q003900012Q001800055Q00201900050005000100201900050005000A2Q003400063Q000900201900070004000B0010080006000B000700201900070004000C0010080006000C000700201900070004000D0010080006000D000700201900070004000E0010080006000E000700201900070004000F0010080006000F00070020190007000400100010080006001000070020190007000400110010080006001100070020190007000400120010080006001200070020190007000400130010080006001300072Q002700050004000600061F3Q000A000100020004253Q000A00012Q00333Q00017Q00113Q0003063Q0069706169727303083Q004E6F5265636F696C030B3Q00576561706F6E436163686503083Q0053652Q74696E677303073Q0047756E4D6F647303063Q005265636F696C028Q0003163Q0043616D6572615265636F696C696E67456E61626C65640100030A3Q00416E676C65585F4D696E030A3Q00416E676C65585F4D6178030A3Q00416E676C65595F4D696E030A3Q00416E676C65595F4D6178030A3Q00416E676C655A5F4D696E030A3Q00416E676C655A5F4D617803063Q00537072656164030C3Q00537072656164416D6F756E7400253Q00121B3Q00014Q001800015Q0020190001000100020020190001000100032Q00213Q000200020004253Q002200012Q001800055Q0020190005000500020020190005000500040020190005000500050020190005000500020006360005001500013Q0004253Q001500010030170004000600070030170004000800090030170004000A00070030170004000B00070030170004000C00070030170004000D00070030170004000E00070030170004000F00072Q001800055Q0020190005000500020020190005000500040020190005000500050020190005000500100006360005002200013Q0004253Q002200012Q001800055Q00201900050005000200201900050005000400201900050005000500201900050005001100100800040010000500061F3Q0006000100020004253Q000600012Q00333Q00017Q00043Q0003053Q00706169727303083Q004E6F5265636F696C030E3Q004F726967696E616C56616C75657303053Q007063612Q6C00113Q00121B3Q00014Q001800015Q0020190001000100020020190001000100032Q00213Q000200020004253Q000E00010006360003000D00013Q0004253Q000D000100121B000500043Q00061A00063Q000100022Q00353Q00034Q00353Q00044Q00020005000200012Q001000035Q00061F3Q0006000100020004253Q000600012Q00333Q00013Q00013Q00093Q0003063Q005265636F696C03163Q0043616D6572615265636F696C696E67456E61626C6564030A3Q00416E676C65585F4D696E030A3Q00416E676C65585F4D6178030A3Q00416E676C65595F4D696E030A3Q00416E676C65595F4D6178030A3Q00416E676C655A5F4D696E030A3Q00416E676C655A5F4D617803063Q0053707265616400254Q00188Q0018000100013Q0020190001000100010010083Q000100012Q00188Q0018000100013Q0020190001000100020010083Q000200012Q00188Q0018000100013Q0020190001000100030010083Q000300012Q00188Q0018000100013Q0020190001000100040010083Q000400012Q00188Q0018000100013Q0020190001000100050010083Q000500012Q00188Q0018000100013Q0020190001000100060010083Q000600012Q00188Q0018000100013Q0020190001000100070010083Q000700012Q00188Q0018000100013Q0020190001000100080010083Q000800012Q00188Q0018000100013Q0020190001000100090010083Q000900012Q00333Q00017Q00053Q0003083Q004E6F5265636F696C03073Q00456E61626C656403043Q007461736B03043Q0077616974029A5Q99B93F010E4Q001800015Q0020190001000100010020190001000100020006360001000D00013Q0004253Q000D000100121B000100033Q00201900010001000400122E000200054Q00020001000200012Q0018000100014Q002A0001000100012Q0018000100024Q002A0001000100012Q00333Q00017Q000E3Q0003063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C030A3Q004368696C64412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E7365727403083Q004E6F5265636F696C030B3Q00436F2Q6E656374696F6E73030C3Q0057616974466F724368696C6403083Q0048756D616E6F6964027Q004003043Q004469656401303Q00121B000100013Q00202D00023Q00022Q001C000200034Q000C00013Q00030004253Q000D000100202D00060005000300122E000800044Q000B0006000800020006360006000D00013Q0004253Q000D00012Q001800066Q0029000700054Q000200060002000100061F00010005000100020004253Q0005000100201900013Q000500202D00010001000600061A00033Q000100012Q000E8Q000B00010003000200121B000200073Q0020190002000200082Q0018000300013Q00201900030003000900201900030003000A2Q0029000400014Q001400020004000100202D00023Q000B00122E0004000C3Q00122E0005000D4Q000B0002000500020006360002002F00013Q0004253Q002F000100201900030002000E00202D00030003000600061A00050001000100032Q000E3Q00014Q000E3Q00024Q000E3Q00034Q000B00030005000200121B000400073Q0020190004000400082Q0018000500013Q00201900050005000900201900050005000A2Q0029000600034Q00140004000600012Q00333Q00013Q00023Q00023Q002Q033Q0049734103043Q00542Q6F6C01093Q00202D00013Q000100122E000300024Q000B0001000300020006360001000800013Q0004253Q000800012Q001800016Q002900026Q00020001000200012Q00333Q00017Q00053Q0003083Q004E6F5265636F696C03073Q00456E61626C656403043Q007461736B03043Q0077616974026Q00F83F000E4Q00187Q0020195Q00010020195Q00020006363Q000D00013Q0004253Q000D000100121B3Q00033Q0020195Q000400122E000100054Q00023Q000200012Q00183Q00014Q002A3Q000100012Q00183Q00024Q002A3Q000100012Q00333Q00017Q000B3Q0003083Q004E6F5265636F696C03073Q00456E61626C65642Q01030B3Q00576561706F6E4361636865030E3Q004F726967696E616C56616C756573030E3Q00436861726163746572412Q64656403073Q00436F2Q6E65637403053Q007461626C6503063Q00696E73657274030B3Q00436F2Q6E656374696F6E7303093Q00436861726163746572002A4Q00187Q0020195Q00010020195Q00020006363Q000600013Q0004253Q000600012Q00333Q00014Q00187Q0020195Q00010030173Q000200032Q00187Q0020195Q00012Q003400015Q0010083Q000400012Q00187Q0020195Q00012Q003400015Q0010083Q000500012Q00183Q00014Q002A3Q000100012Q00183Q00024Q002A3Q000100012Q00183Q00033Q0020195Q000600202D5Q00072Q0018000200044Q000B3Q0002000200121B000100083Q0020190001000100092Q001800025Q00201900020002000100201900020002000A2Q002900036Q00140001000300012Q0018000100033Q00201900010001000B0006360001002900013Q0004253Q002900012Q0018000100044Q0018000200033Q00201900020002000B2Q00020001000200012Q00333Q00017Q00063Q0003083Q004E6F5265636F696C03073Q00456E61626C6564010003063Q00697061697273030B3Q00436F2Q6E656374696F6E73030A3Q00446973636F2Q6E656374001A4Q00187Q0020195Q00010020195Q000200064Q0006000100010004253Q000600012Q00333Q00014Q00187Q0020195Q00010030173Q000200032Q00183Q00014Q002A3Q0001000100121B3Q00044Q001800015Q0020190001000100010020190001000100052Q00213Q000200020004253Q0013000100202D0005000400062Q000200050002000100061F3Q0011000100020004253Q001100012Q00187Q0020195Q00012Q003400015Q0010083Q000500012Q00333Q00017Q00043Q0003083Q004E6F5265636F696C03083Q0053652Q74696E677303073Q0047756E4D6F647303063Q0053707265616403163Q0006360001000700013Q0004253Q000700012Q001800035Q0020190003000300010020190003000300020020190003000300030010080003000100010006360002000E00013Q0004253Q000E00012Q001800035Q0020190003000300010020190003000300020020190003000300030010080003000400020006363Q001300013Q0004253Q001300012Q0018000300014Q002A0003000100010004253Q001500012Q0018000300024Q002A0003000100012Q00333Q00017Q00", GetFEnv(), ...);
