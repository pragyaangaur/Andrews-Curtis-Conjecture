import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 103 of the cap-16 certificate: slots 105472 .. 106495 -/
theorem chk_103 : chunkCheck 16 T stdSt 105472 1024 = true := by decide +kernel

end Row16
