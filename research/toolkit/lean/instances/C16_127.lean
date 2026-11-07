import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 127 of the cap-16 certificate: slots 130048 .. 131071 -/
theorem chk_127 : chunkCheck 16 T stdSt 130048 1024 = true := by decide +kernel

end Row16
