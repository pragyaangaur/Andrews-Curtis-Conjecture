import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 40 of the cap-16 certificate: slots 40960 .. 41983 -/
theorem chk_40 : chunkCheck 16 T stdSt 40960 1024 = true := by decide +kernel

end Row16
