"""
test wishbone peripheral
"""

import cocotb
from cocotb.clock import Clock
from cocotb.binary import BinaryValue
from cocotb.triggers import RisingEdge, FallingEdge, ClockCycles
from cocotbext.wishbone.driver import WishboneMaster, WBOp

# from J Pallent: 
# https://github.com/thejpster/zube/blob/9299f0be074e2e30f670fd87dec2db9c495020db/test/test_zube.py
async def test_wb_set(wbs, addr, value):
    """
    Test putting values into the given wishbone address.
    """
    await wbs.send_cycle([WBOp(addr, value)])

async def test_wb_get(wbs, addr):
    """
    Test getting values from the given wishbone address.
    """
    res_list = await wbs.send_cycle([WBOp(addr)])
    rvalues = [entry.datrd for entry in res_list]
    return rvalues[0]

async def reset(dut):
    dut.reset = 1
    dut.i_wb_data = 0
    dut.buttons = BinaryValue('000')
    await ClockCycles(dut.clk, 5)
    dut.reset = 0
    await ClockCycles(dut.clk, 5)

@cocotb.test()
async def test_all(dut):
    """
    Run all the tests
    """
    clock = Clock(dut.clk, 10, units="us")

    cocotb.fork(clock.start())

    signals_dict = {
        "cyc":  "i_wb_cyc",
        "stb":  "i_wb_stb",
        "we":   "i_wb_we",
        "adr":  "i_wb_addr",
        "datwr":"i_wb_data",
        "datrd":"o_wb_data",
        "ack":  "o_wb_ack"
    }
    wbs = WishboneMaster(dut, "", dut.clk, width=32, timeout=10, signals_dict=signals_dict)

    await reset(dut)

    # Set up our memory addresses for both sides
    led_addr = 0x3000_0000
    but_addr = 0x3000_0004

    # leds
    leds = await test_wb_get(wbs, led_addr)
    assert leds == 0

    # set leds and check they're on
    await test_wb_set(wbs, led_addr, BinaryValue('11111111'))
    leds = await test_wb_get(wbs, led_addr)
    assert leds == BinaryValue('11111111')
    assert dut.leds == BinaryValue('11111111')

    # buttons
    buts = await test_wb_get(wbs, but_addr)
    assert buts == 0

    # press buttons and check we can read the value
    dut.buttons = BinaryValue('111')
    buts = await test_wb_get(wbs, but_addr)
    assert buts == BinaryValue('111')
