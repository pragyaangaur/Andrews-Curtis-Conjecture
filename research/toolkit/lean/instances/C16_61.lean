import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 61 of the cap-16 certificate: slots 62464 .. 63487 -/
theorem chk_61 : chunkCheck 16 T stdSt 62464 1024 = true := by decide +kernel

end Row16
