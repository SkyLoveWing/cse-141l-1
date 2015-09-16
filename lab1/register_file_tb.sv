`timescale 1ns / 1ps

/*
 * CSE141L Lab1: Tools of the Trade
 * University of California, San Diego
 * 
 * Written by Matt DeVuyst, 3/30/2010
 * Modified by Vikram Bhatt, 30/3/2010
 * Modified by Nikolaos Strikos, 4/8/2012
 */

//
// NOTE: This verilog is non-synthesizable.
// You can only use constructs like "initial", "#10", "forever"
// inside your test bench! Do not use it in your actual design.
//

module register_file_tb#(parameter r = 8, parameter w = 16);

	logic clk; //clock
	logic wen_i; //write enabled
	logic [2:0] wa_i; //write address
	logic [w-1:0] wd_i; //write data
	logic [2:0] ra0_i, ra1_i;  //read addresses
	logic [w-1:0] rd0_o, rd1_o; //read data

   // The design under test is our adder
   register_file dut (
				.clk(clk)
	        ,.wen_i(wen_i)
	        ,.wa_i(wa_i)
           ,.wd_i(wd_i)
           ,.ra0_i(ra0_i)
			  ,.ra1_i(ra1_i)
           ,.rd0_o(rd0_o)
           ,.rd1_o(rd1_o)
   );

   // Toggle the clock every 10 ns

   initial
     begin
        clk = 0;
        forever #10 clk = !clk;
     end

   // Test with a variety of inputs.
   // Introduce new stimulus on the falling clock edge so that values
   // will be on the input wires in plenty of time to be read by
   // registers on the subsequent rising clock edge.
   initial
     begin
	  wen_i = 1;
	  
	  wa_i = 2;
	  wd_i = 5;
	  @(negedge clk);
	  wa_i = 3;
	  wd_i = 6;
	  @(negedge clk);
	  ra0_i = 2;
	  ra1_i = 3;
	  @(negedge clk);
	  ra0_i = 3;
	  ra1_i = 3;
	  @(negedge clk);
	  ra0_i = 2;
	  ra1_i = 2;
	  @(negedge clk);
	  wa_i = 3;
	  wd_i = 15;
	  ra0_i = 3;
	  @(negedge clk);
	  wen_i = 0;
	  wa_i = 3;
	  wd_i = 7;
	  ra0_i = 3;
	  
     end // initial begin

endmodule // test_adder
