/*
    based off https://zipcpu.com/zipcpu/2017/05/29/simple-wishbone.html

    copyright Matt Venn 2020

    licensed under the GPL
*/
`default_nettype none
`timescale 1ns/1ns

module wb_buttons_leds #(
    parameter   [31:0]  BASE_ADDRESS    = 32'h3000_0000,        // base address
    parameter   [31:0]  LED_ADDRESS     = BASE_ADDRESS,
    parameter   [31:0]  BUTTON_ADDRESS  = BASE_ADDRESS + 4
    ) (
`ifdef USE_POWER_PINS
    inout vccd1,	// User area 1 1.8V supply
    inout vssd1,	// User area 1 digital ground
`endif
    input wire          clk,
    input wire          reset,

    // wb interface
    input wire          i_wb_cyc,       // wishbone transaction
    input wire          i_wb_stb,       // strobe - data valid and accepted as long as !o_wb_stall
    input wire          i_wb_we,        // write enable
    input wire  [31:0]  i_wb_addr,      // address
    input wire  [31:0]  i_wb_data,      // incoming data
    output reg          o_wb_ack,       // request is completed 
    output wire         o_wb_stall,     // cannot accept req
    output reg  [31:0]  o_wb_data,      // output data

    // buttons
    input wire  [2:0]   buttons,
    output reg  [7:0]   leds

    );

    assign o_wb_stall = 0;

    initial leds = 8'b0;

    // writes
    always @(posedge clk) begin
        if(reset)
            leds <= 8'b0;
        else if(i_wb_stb && i_wb_cyc && i_wb_we && !o_wb_stall && i_wb_addr == LED_ADDRESS) begin
            leds <= i_wb_data[7:0];
        end
    end

    // reads
    always @(posedge clk) begin
        if(reset)
            o_wb_data <= 0;
        else if(i_wb_stb && i_wb_cyc && !i_wb_we && !o_wb_stall)
            case(i_wb_addr)
                LED_ADDRESS: 
                    o_wb_data <= {24'b0, leds};
                BUTTON_ADDRESS: 
                    o_wb_data <= {29'b0, buttons};
                default:
                    o_wb_data <= 32'b0;
            endcase
    end

    // acks
    always @(posedge clk) begin
        if(reset)
            o_wb_ack <= 0;
        else
            // return ack immediately
            o_wb_ack <= (i_wb_stb && !o_wb_stall && (i_wb_addr == LED_ADDRESS || i_wb_addr == BUTTON_ADDRESS));
    end

endmodule
