import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 42 of the cap-16 certificate: slots 43008 .. 44031 -/
theorem chk_42 : chunkCheck 16 T stdSt 43008 1024 = true := by decide +kernel

end Row16
