import EthBridge.WordRAM

#check @EthBridge.WordRAM.not_eth_ram
#check @EthBridge.WordRAM.RAMDecidableInExpTime
#check @EthBridge.WordRAM.ETH_RAM

example : ¬ EthBridge.WordRAM.ETH_RAM :=
  EthBridge.WordRAM.not_eth_ram

#print axioms EthBridge.WordRAM.not_eth_ram
#print axioms EthBridge.WordRAM.Sim.executes_simProgram_of_space
#print axioms EthBridge.WordRAM.Decide.uniformDecidable_of_timeSpace
#print axioms EthBridge.WordRAM.Decider.exists_ksat3_decider
