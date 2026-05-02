## MLK-S02-100T Assumed Constraint Profile
##
## WARNING:
## - non-authoritative
## - derived from unverified secondary claims, not from the vendor archive
## - intended only for assumption-driven scaffolding work
## - do not treat this file as board validation evidence
##
## Rationale:
## - keep the repo-default `mlk_s02_100t.xdc` as an explicit placeholder
## - allow provisional iteration against a concrete guessed pin set
##
## Assumed facts used here:
## - board: MiLianKe MLK-S02-100T
## - FPGA tool target under test: xc7a100tfgg484-2
## - assumed pin-map source still came from unverified secondary claims
## - assumed system clock pin claim: W19
## - assumed reset pin claim: V18
## - assumed UART RX pin claim: L19
## - assumed UART TX pin claim: L20
## - assumed LED0 pin claim: M22
## - assumed clock frequency claim: 50 MHz
##
## Note:
## The repo board contract still uses the logical port name `clk25`.
## This file preserves that port name for compatibility, but drives it with
## the assumed external clock pin and an assumed 50 MHz period.

## Assumed primary system clock
set_property PACKAGE_PIN W19 [get_ports clk25]
set_property IOSTANDARD LVCMOS33 [get_ports clk25]
create_clock -period 20.000 -name sys_clk_assumed_50m [get_ports clk25]

## Assumed active-low reset
set_property PACKAGE_PIN V18 [get_ports rst_n]
set_property IOSTANDARD LVCMOS33 [get_ports rst_n]

## Assumed CH340-connected UART
set_property PACKAGE_PIN L20 [get_ports uart_tx]
set_property IOSTANDARD LVCMOS33 [get_ports uart_tx]
set_property PACKAGE_PIN L19 [get_ports uart_rx]
set_property IOSTANDARD LVCMOS33 [get_ports uart_rx]

## Only LED0 was supplied in the unverified claim set.
## The remaining LED and button pins are intentionally left commented until
## a real board archive or schematic confirms them.
set_property PACKAGE_PIN M22 [get_ports {led[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {led[0]}]

## Unverified placeholders retained explicitly:
## set_property PACKAGE_PIN <LED1_PIN> [get_ports {led[1]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[1]}]
## set_property PACKAGE_PIN <LED2_PIN> [get_ports {led[2]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[2]}]
## set_property PACKAGE_PIN <LED3_PIN> [get_ports {led[3]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[3]}]
## set_property PACKAGE_PIN <LED4_PIN> [get_ports {led[4]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[4]}]
## set_property PACKAGE_PIN <LED5_PIN> [get_ports {led[5]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[5]}]
## set_property PACKAGE_PIN <LED6_PIN> [get_ports {led[6]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[6]}]
## set_property PACKAGE_PIN <LED7_PIN> [get_ports {led[7]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {led[7]}]

## set_property PACKAGE_PIN <BTN0_PIN> [get_ports {btn[0]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {btn[0]}]
## set_property PACKAGE_PIN <BTN1_PIN> [get_ports {btn[1]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {btn[1]}]
## set_property PACKAGE_PIN <BTN2_PIN> [get_ports {btn[2]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {btn[2]}]
## set_property PACKAGE_PIN <BTN3_PIN> [get_ports {btn[3]}]
## set_property IOSTANDARD LVCMOS33 [get_ports {btn[3]}]
