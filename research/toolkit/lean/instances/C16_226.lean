import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 226 of the cap-16 certificate: slots 231424 .. 232447 -/
theorem chk_226 : chunkCheck 16 T stdSt 231424 1024 = true := by decide +kernel

end Row16
