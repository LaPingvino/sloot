package graph

import (
	"bufio"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
)

// Job is one module to extract: its name and base .olean path.
type Job struct{ Mod, OLean string }

// Extract runs the extractor binary over jobs and writes one gzip shard per
// module into store/graph. Shards that already exist and are newer than the
// module's .olean are skipped, so an interrupted run resumes.
func Extract(extractor, store string, env []string, jobs []Job, log io.Writer) (done int, err error) {
	if err := os.MkdirAll(filepath.Join(store, "graph"), 0o755); err != nil {
		return 0, err
	}
	var todo []Job
	for _, j := range jobs {
		if fresh(ShardPath(store, j.Mod), j.OLean) {
			continue
		}
		todo = append(todo, j)
	}
	if len(todo) == 0 {
		return 0, nil
	}
	cmd := exec.Command(extractor, "graph")
	cmd.Env = append(os.Environ(), env...)
	cmd.Stderr = log
	in, err := cmd.StdinPipe()
	if err != nil {
		return 0, err
	}
	out, err := cmd.StdoutPipe()
	if err != nil {
		return 0, err
	}
	if err := cmd.Start(); err != nil {
		return 0, err
	}
	go func() {
		w := bufio.NewWriter(in)
		for _, j := range todo {
			fmt.Fprintf(w, "%s\t%s\n", j.Mod, j.OLean)
		}
		w.Flush()
		in.Close()
	}()

	var (
		curMod string
		curF   *os.File
		curZ   *gzip.Writer
	)
	closeCur := func() error {
		if curZ == nil {
			return nil
		}
		if err := curZ.Close(); err != nil {
			return err
		}
		tmp := curF.Name()
		if err := curF.Close(); err != nil {
			return err
		}
		done++
		curZ = nil
		return os.Rename(tmp, ShardPath(store, curMod))
	}
	sc := bufio.NewScanner(out)
	sc.Buffer(make([]byte, 1<<20), 1<<28)
	for sc.Scan() {
		line := sc.Bytes()
		var head struct{ T, M, E string }
		if err := json.Unmarshal(line, &head); err != nil {
			return done, fmt.Errorf("bad extractor line: %w", err)
		}
		if head.T == "err" {
			fmt.Fprintf(log, "extract %s: %s\n", head.M, head.E)
			continue
		}
		if head.M != curMod {
			if err := closeCur(); err != nil {
				return done, err
			}
			curMod = head.M
			curF, err = os.Create(ShardPath(store, curMod) + ".tmp")
			if err != nil {
				return done, err
			}
			curZ = gzip.NewWriter(curF)
		}
		curZ.Write(line)
		curZ.Write([]byte{'\n'})
	}
	if err := closeCur(); err != nil {
		return done, err
	}
	if err := sc.Err(); err != nil {
		return done, err
	}
	return done, cmd.Wait()
}

func fresh(shard, olean string) bool {
	s, err := os.Stat(shard)
	if err != nil {
		return false
	}
	o, err := os.Stat(olean)
	if err != nil {
		return true
	}
	return !s.ModTime().Before(o.ModTime())
}
