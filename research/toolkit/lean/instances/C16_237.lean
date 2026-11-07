import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 237 of the cap-16 certificate: slots 242688 .. 243711 -/
theorem chk_237 : chunkCheck 16 T stdSt 242688 1024 = true := by decide +kernel

end Row16
