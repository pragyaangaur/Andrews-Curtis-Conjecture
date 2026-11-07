import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 96 of the cap-16 certificate: slots 98304 .. 99327 -/
theorem chk_96 : chunkCheck 16 T stdSt 98304 1024 = true := by decide +kernel

end Row16
