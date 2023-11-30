/*
    based off https://zipcpu.com/zipcpu/2017/05/29/simple-wishbone.html

    copyright Matt Venn 2020

    licensed under the GPL
*/
`default_nettype none
module wb_buttons_leds #(
    parameter   [31:0]  BASE_ADDRESS    = 32'h3000_0000,        // base address
    parameter   [31:0]  LED_ADDRESS     = BASE_ADDRESS,
    parameter   [31:0]  BUTTON_ADDRESS  = BASE_ADDRESS + 4
    ) (
    input wire          wb_clk_i,
    input wire          wb_rst_i,

    // wb interface
    input wire          wbs_cyc_i,       // wishbone transaction
    input wire          wbs_stb_i,       // strobe - data valid and accepted as long as !wbs_sta_o
    input wire          wbs_we_i,        // write enable
    input wire  [31:0]  wbs_adr_i,      // address
    input wire  [31:0]  wbs_dat_i,      // incoming data
    output reg          wbs_ack_o,       // request is completed 
    output wire         wbs_sta_o,     // cannot accept req
    output reg  [31:0]  wbs_dat_o,      // output data

    // buttons
    input wire  [7:0]   buttons,
    output reg  [7:0]   leds,
    output wire [15:0]   oeb
    );

    assign wbs_sta_o = 0;
    assign oeb = 16'b0000000011111111;

    // writes
    always @(posedge wb_clk_i) begin
        if(wb_rst_i)
            leds <= 8'b0;
        else if(wbs_stb_i && wbs_cyc_i && wbs_we_i && !wbs_sta_o && wbs_adr_i == LED_ADDRESS) begin
            leds <= wbs_dat_i[7:0];
        end
    end

    // reads
    always @(posedge wb_clk_i) begin
        if(wbs_stb_i && wbs_cyc_i && !wbs_we_i && !wbs_sta_o)
            case(wbs_adr_i)
                LED_ADDRESS: 
                    wbs_dat_o <= {24'b0, leds};
                BUTTON_ADDRESS: 
                    wbs_dat_o <= {24'b0, buttons};
                default:
                    wbs_dat_o <= 32'b0;
            endcase
    end

    // acks
    always @(posedge wb_clk_i) begin
        if(wb_rst_i)
            wbs_ack_o <= 0;
        else
            // return ack immediately
            wbs_ack_o <= (wbs_stb_i && !wbs_sta_o && (wbs_adr_i == LED_ADDRESS || wbs_adr_i == BUTTON_ADDRESS));
    end

`ifdef FORMAL
    default clocking @(posedge wb_clk_i); endclocking
    default disable iff (wb_rst_i);

    cyc:    assume property (wbs_cyc_i |=> wbs_cyc_i && wbs_ack_o);
    write:  cover property (##1 $rose(wbs_stb_i) |-> ##[+] wbs_dat_o[3:0] == 4'b1010);
    read:   cover property (##1 $rose(wbs_stb_i) |-> ##[+] leds[7:0] == 8'b11110000);
`endif
endmodule
