import EthBridge.OpenAIChain
import EthBridge.AnthropicChain
import EthBridge.Elementary.ReusedRecursion
import EthBridge.WordRAM

example : ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH :=
  EthBridge.OpenAIChain.not_eth

example : ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH :=
  EthBridge.AnthropicChain.not_eth

example : ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH :=
  EthBridge.Elementary.ReusedRecursion.not_eth

example : ¬ EthBridge.WordRAM.ETH_RAM := EthBridge.WordRAM.not_eth_ram

#print axioms EthBridge.OpenAIChain.not_eth
#print axioms EthBridge.AnthropicChain.not_eth
#print axioms EthBridge.Elementary.ReusedRecursion.not_eth
#print axioms EthBridge.WordRAM.not_eth_ram
