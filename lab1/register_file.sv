module register_file#(parameter r = 8, parameter w = 16)
(
 input clk, //clock
 input wen_i, //write enabled
 input [2:0] wa_i, //write address
 input [w-1:0] wd_i, //write data
 input [2:0] ra0_i, ra1_i, //read addresses
 output [w-1:0] rd0_o, rd1_o //read data
);
	
	logic [w-1:0] rf[0:r-1];
	
	assign rd0_o = rf[ra0_i];
	assign rd1_o = rf[ra1_i];

   always_ff @(posedge clk)
		begin
			if(wen_i == 1) begin
				rf[wa_i] = wd_i;
			end
		end

endmodule
