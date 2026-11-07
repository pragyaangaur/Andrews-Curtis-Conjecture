import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 253 of the cap-16 certificate: slots 259072 .. 260095 -/
theorem chk_253 : chunkCheck 16 T stdSt 259072 1024 = true := by decide +kernel

end Row16
