"""
Copyright Matt Venn 2023
"""

from caravel_cocotb.caravel_interfaces import test_configure
from caravel_cocotb.caravel_interfaces import report_test
import cocotb

@cocotb.test()
@report_test
async def wishbone_test(dut):
    caravelEnv = await test_configure(dut, timeout_cycles=200000)

    cocotb.log.info(f"[TEST] set all buttons low") 
    caravelEnv.drive_gpio_in((15,8), 0x00)

    cocotb.log.info(f"[TEST] wait for configuration")  
    await caravelEnv.release_csb()
    await caravelEnv.wait_mgmt_gpio(1)
    cocotb.log.info(f"[TEST] finished configuration") 

    for i in range(16):
        # cocotb.log.info(f"[TEST] set buttons to {i}") 
        caravelEnv.drive_gpio_in((15,8), i)

        # sync with firmware
        await caravelEnv.wait_mgmt_gpio(0)
        await caravelEnv.wait_mgmt_gpio(1)

        # read the led outputs - should match the buttons
        leds = int ((caravelEnv.monitor_gpio(23,16).binstr),2)
        # gpios 31:24 should also match the buttons
        gpios = int ((caravelEnv.monitor_gpio(31,24).binstr),2)
        cocotb.log.info(f"[TEST] buttons set to {i}. gpio are {gpios} leds are {leds}") 
        
        if leds != i:
            cocotb.log.error(f"leds not the same as buttons!")
        if gpios != i:
            cocotb.log.error(f"mgmt controlled gpios not the same as buttons!")

    # extra 1000 cycles to make it easier to see the end of the trace
    await cocotb.triggers.ClockCycles(caravelEnv.clk, 1000)
